include "Io.dfy"
class LZSS {    
    static const BITFLAG_WORD: bit := 0;
    static const BITFLAG_PAIR: bit := 1;
    static const LOOKAHEAD := (2, 4);
    static const SEARCH := (6, 64);
    static const WINDOW := (LOOKAHEAD.0+SEARCH.0, LOOKAHEAD.1*SEARCH.1);
    static const BYTE := (8, 256);

    static method ArrayFromSeq<A>(s: seq<A>) returns (a: array<A>)
        ensures a[..] == s
    {
        a := new A[|s|] ( i requires 0 <= i < |s| => s[i] );
    }
    
    static method MatchLength(buffer: array<byte>, position1: int, position2: int) returns(mlength: int)
        requires 0 <= position1 < position2 < buffer.Length-1
        requires buffer[position1] == buffer[position2]
        ensures 1 <= mlength <= WINDOW.1
        ensures position2 + mlength < buffer.Length
        ensures buffer[position1..position1+mlength] == buffer[position2..position2+mlength]
    {
        mlength := 1;
        while mlength < WINDOW.1 && position2 + mlength < buffer.Length-1 && buffer[position1 + mlength] == buffer[position2 + mlength]
            decreases WINDOW.1 - mlength
            invariant mlength <= WINDOW.1
            invariant position2 + mlength <= buffer.Length-1
            invariant buffer[position1..position1+mlength] == buffer[position2..position2+mlength]
        {
            mlength := mlength + 1;
        }
    }

    static method LongestMatch(buffer: array<byte>, position: int) returns(match_: bool, offset: int, size: int)
        requires 0 < position < buffer.Length
        ensures 1 <= offset < SEARCH.1
        ensures match_ ==> 0 < size <= WINDOW.1
        ensures position - offset + size <= buffer.Length
        ensures 0 <= position - offset
        ensures position + size <= buffer.Length
        ensures match_ ==> buffer[position..position+size] == buffer[position-offset..position-offset+size]
    {
        offset := 1;
        size := 0;

        var cOffset := 1;

        while cOffset < SEARCH.1 && 0 <= position - cOffset && position + size < buffer.Length - 1
            decreases SEARCH.1 - cOffset
            invariant size <= WINDOW.1
            invariant offset < SEARCH.1
            invariant 0 <= position - offset
            invariant position + size <= buffer.Length
            invariant buffer[position..position+size] == buffer[position-offset..position-offset+size]
        {
            if(buffer[position] == buffer[position-cOffset]) {
                var mlength := MatchLength(buffer, position - cOffset, position);
                offset := if size >= mlength then offset else cOffset;
                size := if size >= mlength then size else mlength;
            }
            cOffset := cOffset + 1;
        }

        match_ := !(size == 0);
    }

    static method BitsToByte(bits: seq<bit>) returns(b: byte)
        requires 1 <= |bits| <= BYTE.0
        //ensures ByteToBits() == bits
    {
        b := 0;

        var iter := |bits|-1;
        var exp2: byte := 1;

        while 0 <= iter < |bits|
            decreases iter - 0
        {
            if b as int + exp2 as int >= BYTE.1 {break;} // should never happen
            b := b + if bits[iter] == 1 then exp2 else 0;

            if exp2 as int *2 >= BYTE.1 {break;} // should never happen
            exp2 := exp2*2;
            iter := iter - 1;
        }
    }

    static method BitsToBytes(bits: seq<bit>) returns(bytes: seq<byte>)
        ensures 1 <= |bits| ==> |bits|/BYTE.0 == |bytes| || |bits|/BYTE.0 + 1 == |bytes|
        //ensures BytesToBits() == bits
    {
        bytes := [];
        if |bits| == 0 {return;}

        var nbyte;
        var iter := 0;
        var xpto := bits;
        while iter + BYTE.0 < |bits|
            decreases |bits| - iter
            invariant 0 <= iter < |bits|
            invariant iter/BYTE.0 == |bytes|
        {
            nbyte := BitsToByte(bits[iter..iter+BYTE.0]);
            bytes := bytes + [nbyte];
            iter := iter + BYTE.0;
        }
        nbyte := BitsToByte(bits[iter..]);
        bytes := bytes + [nbyte];
    }

    static method ByteToBits(b: byte, bitsToConvert: int) returns(bits: seq<bit>)
        requires 0 <= bitsToConvert <= BYTE.0
        ensures |bits| == bitsToConvert
        //ensures BitsToByte() == b
    {
        bits := [];

        var iter := 0;
        var exp2 := b;

        while iter < bitsToConvert
            decreases bitsToConvert - iter
            invariant |bits| == iter
        {
            bits := (if exp2%2 == 0 then [0] else [1]) + bits;
            
            exp2 := exp2/2;
            iter := iter + 1;
        }

        bits := bits[0..bitsToConvert];
    }

    static method BytesToBits(bytes: seq<byte>, bitsToConvert: int) returns(bits: seq<bit>)
        requires (|bytes|-1) * BYTE.0 <= bitsToConvert <= |bytes| * BYTE.0
        //ensures BitsToBytes() == b
    {
        bits := [];
        if |bytes| == 0 { return; }
        
        var nbits;
        var iter := 0;
        var toConvert := 0;
        
        while iter < |bytes| - 1
            decreases |bytes| - iter
            invariant iter < |bytes|
            invariant iter*BYTE.0 == toConvert
        {
            toConvert := toConvert + BYTE.0;
            nbits := ByteToBits(bytes[iter], BYTE.0);
            bits := bits + nbits;
            iter := iter + 1;
        }

        nbits := ByteToBits(bytes[iter], bitsToConvert-toConvert);
        bits := bits + nbits;
    }

    static method {:autoReq} Encode(from: array<byte>) returns(to: seq<byte>)
    {
        to := [];
        if from.Length == 0 {return;}

        var bits := [];
        var pointer: int := 0;
        
        /*print("(0,");
        print(from[pointer]);
        print(")\n");*/

        bits := bits + [BITFLAG_WORD];
        var word_bits := ByteToBits(from[pointer], BYTE.0); assert BYTE.0 <= 8;
        bits := bits + word_bits;
        pointer := pointer + 1;

        while pointer < from.Length
            decreases from.Length - pointer
        {
            var match_, offset, len := LongestMatch(from, pointer);

            if match_ && len*(SEARCH.0 + WINDOW.0 + BYTE.0) >= len*(BYTE.0+1) {
                //<1,offset,len,word>
                /*print("(1,");
                print(offset);
                print(",");
                print(len);
                print(",");
                print(from[pointer+len]);
                print(")\n");*/

                bits := bits + [BITFLAG_PAIR];
                var offset_bits := ByteToBits(offset as byte, SEARCH.0); assert SEARCH.0 <= 8;
                bits := bits + offset_bits;
                var len_bits := ByteToBits((len as int -1) as byte, WINDOW.0); assert WINDOW.0 <= 8;
                bits := bits + len_bits;
                pointer := pointer + len;

                if pointer >= from.Length {return;}//!!!!
                var word_bits := ByteToBits(from[pointer] as byte, BYTE.0); assert BYTE.0 <= 8;
                bits := bits + word_bits;
                pointer := pointer + 1;
            } else {
                //<0,word>
                /*print("(0,");
                print(from[pointer]);
                print(")\n");*/

                bits := bits + [BITFLAG_WORD];
                var word_bits := ByteToBits(from[pointer], BYTE.0); assert BYTE.0 <= 8;
                bits := bits + word_bits;
                pointer := pointer + 1;
            }
        }
        
        to := BitsToBytes(bits+[0,0,0,0,0,0]);
    }

    static method {:autoReq} Decode(from: array<byte>) returns(to: seq<byte>)
    {
        to := [];
        if from.Length == 0 { return; }

        var bits := BytesToBits(from[..], from.Length*BYTE.0);

        while |bits| >= 0
            decreases |bits|
        {
            if |bits| < 8 { break; }
            else if bits[0] == BITFLAG_PAIR {
                //<1,offset,len,word>
                bits := bits[1..];

                var offset, len, word;
                
                offset := BitsToByte(bits[0..SEARCH.0]);
                bits := bits[SEARCH.0..];
                if WINDOW.0 >= |bits| {return;}//!!!!!!!!!
                len := BitsToByte(bits[0..WINDOW.0]);
                bits := bits[WINDOW.0..];
                if BYTE.0 >= |bits| {return;}//!!!!!!!!!
                word := BitsToByte(bits[0..BYTE.0]);
                bits := bits[BYTE.0..];

                /*print("[1,");
                print(offset);
                print(",");
                print(len);
                print(",");
                print(word);
                print("]\n");*/

                var i := 0;
                while i <= len as int && 0 <= |to| - offset as int < |to|
                    decreases len as int - i
                {
                    to := to + [to[|to| - offset as int]];
                    i := i + 1;
                }
                
                to := to + [word];
            } else {
                //<0,word>
                bits := bits[1..];
                
                var word;
                if BYTE.0 >= |bits| {return;}//!!!!!!!!!
                word := BitsToByte(bits[0..BYTE.0]);
                bits := bits[BYTE.0..];
                to := to + [word];

                /*print("[0,");
                print(word);
                print("]\n");*/
            }
        }
    }
}