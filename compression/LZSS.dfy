include "Io.dfy"
class LZSS {
    static const BITFLAG_WORD: bit := 0;
    static const BITFLAG_PAIR: bit := 1;
    static const LOOKAHEAD := (4, 16);
    static const SEARCH := (4, 16);
    static const WINDOW := (8, 256); //LOOKAHEAD + SEARCH
    static const BYTE_SIZE := 8; //8 bits

    static method MatchSize(buffer: array<byte>, position1: int, position2: int, ceiling: int) returns(size: int)
        requires 0 <= position1 < position2 <= ceiling <= buffer.Length
        ensures  0 <= size
    {
        size := 0;
        while position1 + size < ceiling && position2 + size < buffer.Length-1 // eof can never match
            decreases ceiling - size
            invariant 0 <= position1 + size <= ceiling <= buffer.Length
        {
            if buffer[position1 + size] != buffer[position2 + size] {break;}
            size := size + 1;
        }
    }

    static method FindBiguestMatch(buffer: array<byte>, position: int) returns(match_: bool, bestOffsetSoFar: int, size: int)
        requires 0 <= position < buffer.Length
        ensures match_ ==> (size >= 0 && bestOffsetSoFar >= 1)
    {
        var offset := 1;

        size := 0;
        match_ := true;
        bestOffsetSoFar := 1;

        var floor := if position - SEARCH.1 >= 0 then position-SEARCH.1 else 0;

        while floor <= position - offset as int
            decreases position - offset as int - floor
        {
            if(buffer[position] == buffer[position-offset as int]) {
                var ceiling := if position + LOOKAHEAD.1 < buffer.Length then position + LOOKAHEAD.1 else buffer.Length-1;
                var newSize := MatchSize(buffer, position - offset as int, position, ceiling);
                bestOffsetSoFar := if size >= newSize then bestOffsetSoFar else offset;
                size := if size >= newSize then size else newSize;
            }
            offset := offset + 1;
        }

        match_ := !(bestOffsetSoFar == 1 && size == 0);
    }

    static method Queue(queue: array<bit>, queuePointer: int, toQueue: int, bitsToQueue: int) returns(nPointer: int)
        requires 0 <= queuePointer < queue.Length
        requires 1 <= bitsToQueue <= 32
        requires 1 <= queuePointer + bitsToQueue <= queue.Length
        modifies queue
    {
        var iter := 1;
        var nb := toQueue;
        nPointer := queuePointer;

        while iter <= bitsToQueue && nPointer < queue.Length
            decreases bitsToQueue - iter
            decreases queue.Length - nPointer
        {
            queue[nPointer+bitsToQueue-iter] := if nb%2 == 1 then 1 as bit else 0 as bit;
            nb := nb/2;
            iter := iter + 1;
        }
        nPointer := nPointer + bitsToQueue;
    }

    static method Flush(to: array<byte>, toSize: int, queue: array<bit>, qpointer: int) returns(ntoSize: int, nqpointer: int)
        requires 0 <= qpointer <= queue.Length
        requires 0 <= toSize + qpointer / BYTE_SIZE <= to.Length
        modifies to, queue;
        //ensures nqpointer < BYTE_SIZE;
    {
        nqpointer := 0;
        ntoSize := toSize;
        
        var toFlush := toSize + qpointer / BYTE_SIZE;
        while ntoSize < toFlush && nqpointer < qpointer
            decreases toFlush - ntoSize
        {
            var exp: byte := 128;
            var i := 0;
            while i < BYTE_SIZE
                decreases BYTE_SIZE - i
            {
                to[ntoSize] := to[ntoSize] + if queue[nqpointer] == 0 then 0 else exp;
                i := i + 1;
                exp := exp/2;
                nqpointer := nqpointer + 1;
            }

            ntoSize := ntoSize + 1;
        }

        var i := 0;
        while i + nqpointer < qpointer
            decreases qpointer - i
        {
            queue[i] := queue[nqpointer+i];
            i := i + 1;
        }

        nqpointer := i;
    }

    static method Encode(from: array<byte>) returns(to: array<byte>, toSize: int)
    {
        toSize := 0;
        to := new byte[from.Length * 2];
       
        var pointer: int := 0;

        var qpointer: int := 0;
        var queue := new bit[128];
        var totalBits := 0;
        while pointer < from.Length
            decreases from.Length - pointer
        {
            var match_, offset, len := FindBiguestMatch(from, pointer);
    
            if match_ {
                //<1,offset,len,word>
                if !(0 <= qpointer < queue.Length) {break;}
                queue[qpointer] := BITFLAG_PAIR;
                qpointer := qpointer + 1;
                
                if !(0 <= qpointer < queue.Length) || !(1 <= qpointer + BYTE_SIZE <= queue.Length) || !(0 <= pointer < from.Length) {break;}
                qpointer := Queue(queue, qpointer, offset as int, SEARCH.0);

                if !(0 <= qpointer < queue.Length) || !(1 <= qpointer + BYTE_SIZE <= queue.Length) || !(0 <= pointer < from.Length) {break;}
                qpointer := Queue(queue, qpointer, len as int, WINDOW.0);
                pointer := pointer + len;
                
                if !(0 <= qpointer < queue.Length) || !(1 <= qpointer + BYTE_SIZE <= queue.Length) || !(0 <= pointer < from.Length) {break;}
                qpointer := Queue(queue, qpointer, from[pointer] as int, BYTE_SIZE);
                pointer := pointer + 1;
            } else {
                //<0,word>
                if !(0 <= qpointer < queue.Length) {break;}
                queue[qpointer] := BITFLAG_WORD;
                qpointer := qpointer + 1;
                if !(0 <= qpointer < queue.Length) || !(1 <= qpointer + BYTE_SIZE <= queue.Length) || !(0 <= pointer < from.Length) {break;}
                qpointer := Queue(queue, qpointer, from[pointer] as int, BYTE_SIZE);
                pointer := pointer + 1;
            }
            if !(0 <= qpointer <= queue.Length) || !(0 <= toSize + qpointer / BYTE_SIZE <= to.Length) {break;}
            toSize, qpointer := Flush(to, toSize, queue, qpointer);
        }
        if qpointer != 0 {
            qpointer := Queue(queue, qpointer, 0, BYTE_SIZE);
            toSize, qpointer := Flush(to, toSize, queue, qpointer);
        }
    }

    static method GetByte(queue: array<bit>, qp: int, bitTo: int) returns(b: byte, nqp: int)
        requires 1 <= bitTo <= 8
    {
        var i := 1;
        var exp := 1;
        while i <= bitTo
            decreases bitTo - i
        {
            b := b + if queue[qp+bitTo-i] == 0 then 0 else exp;
            exp := exp*2;
            i := i + 1;
        }
        nqp := qp + bitTo;
    }
    static method Decode(from: array<byte>) returns(to: array<byte>, toSize: int)
    {
        to := new byte[from.Length * 16];
        var pointer: int := 0;
        var queue: array<bit> := new bit[64];
        var queuePointer: int := 0;
        var qp := 0;
        toSize := 0;

        while true
            //decreases from.Length - pointer
        {
            while queuePointer + BYTE_SIZE < queue.Length && pointer < from.Length
                decreases from.Length - pointer
            {
                queuePointer := LZSS.Queue(queue, queuePointer, from[pointer] as int, BYTE_SIZE);
                pointer := pointer + 1;
            }

            if queuePointer - qp < 8 {break;}
            else if queue[qp] == 1 {
                //<1,offset,len,word>
                qp := qp + 1;
                var offset, len, word;

                if toSize == 8170 {
                    //var a1, a2 := GetByte(queue, qp-8, 8);
                    var j := qp;
                    while j < queue.Length {
                        print(queue[j]);
                        j := j + 1;
                    }
                    print("\n");
                    print(qp);
                    print("-");
                    print(queuePointer);
                    print("-");
                    print(offset);
                    print("-");
                    print(len);
                    print("-");
                    print(word);
                    print("\n");
                }//000000010000000000000001111

                offset, qp := GetByte(queue, qp, SEARCH.0);
                len, qp := GetByte(queue, qp, WINDOW.0);
                word, qp := GetByte(queue, qp, BYTE_SIZE);

                if toSize == 8170 {
                    //var a1, a2 := GetByte(queue, qp-8, 8);
                    print(offset);
                    print("-");
                    print(len);
                    print("-");
                    print(word);
                    print("\n");
                }

                var i: int := 0;
                while i < len as int
                    decreases len as int - i
                {
                    to[toSize + i] := to[toSize - offset as int + i];
                    i := i + 1;
                }

                toSize := toSize + len as int;
                to[toSize] := word;
                toSize := toSize + 1;
            } else {
                //<0,word>
                qp := qp + 1;
                var word;
                word, qp := GetByte(queue, qp, BYTE_SIZE);
                to[toSize] := word;
                toSize := toSize + 1;
            }

            var i := 0;
            while qp + i < queuePointer <= queue.Length
                decreases queuePointer - i
            {
                queue[i] := queue[qp+i];
                i := i + 1;
            }
            queuePointer := i;
            qp := 0;
            
            if qp == queuePointer {break;}
        }
    }
}