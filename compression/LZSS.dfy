include "Io.dfy"
class LZSS {
    // if B == 0 8bits if B == 1 8+4+8=20bits
    // 
    static const BITFLAG_CODEWORD := 0;
    static const BITFLAG_PAIR := 1;
    static const LOOKAHEAD_BUFFER_SIZE := 5;
    static const SEARCH_BUFFER_SIZE := 4;
    static const FLUSH_SIZE := 256;
    static method ShiftInsert(buffer: array<byte>, insert: array<byte>) returns(ret: array<byte>)
    {
        ret := new [buffer.Length];

        var index := 1;
        while index <= buffer.Length
            decreases buffer.Length - index
        {
            ret[index-1] := if index <= buffer.Length - insert.Length
                then buffer[index+insert.Length-1] else insert[insert.Length - (buffer.Length-index + 1)];
            index := index + 1;
        }
    }

    static method GetMatchSize(buffer: array<byte>, pos1: int, pos2: int) returns(len: int)
        requires 0 <= pos1 < pos2 < buffer.Length
        ensures len >= 1
    {
        len := 1;
        while pos2 + len < buffer.Length
            decreases buffer.Length - (len + pos2)
        {
            if buffer[pos1 + len] != buffer[pos2 + len] {break;}
            len := len + 1;
        }
    }
    static method FindBiguestMatch(buffer: array<byte>, pos: int) returns(match_: bool, bestOffsetSoFar: int, len: int)
        requires 0 <= pos < buffer.Length
        ensures 0 <= len
    {
        bestOffsetSoFar := 1;
        var offset := 1;
        match_ := true;
        len := 0;
        
        while pos - offset >= 0
            decreases pos - offset
        {
            if(buffer[pos] == buffer[pos - offset]) {
                var newLen := GetMatchSize(buffer, pos - offset, pos);
                bestOffsetSoFar := if len > newLen then bestOffsetSoFar else offset;
                len := if len > newLen then len else newLen;
            }
            offset := offset + 1;
        }

        if bestOffsetSoFar == 1 && len == 0 {
            match_ := false;
        }
    }
    
    method queueWord(bitflag: int, word: byte)
    {
        print "<";
        print bitflag;
        print ",";
        print word;
        print ">";
    }

    method queuePair(bitflag: int, offset: int, len: int, word: byte)
    {
        print "<";
        print bitflag;
        print ",";
        print offset;
        print ",";
        print len;
        print ",";
        print word;
        print ">";
    }

    constructor () requires true {}
    method encode(from: array<char>, to: array<char>, ghost env:HostEnvironment?)
        requires env != null && env.Valid() && env.ok.ok();
        modifies this;
        modifies env.ok;
        modifies env.files;
    {
        var fromSuccess, fromFs := FileStream.Open(from, env);
        if !fromSuccess {return;}
        var file_offset := 0;
        var success, size: int32 := FileStream.FileLength(from, env);
        if !success {return;}
        var toSuccess, toFs := FileStream.Open(to, env);
        if !toSuccess {return;}
        var outfile_offset := 0;

        //if(size < LOOKAHEAD_BUFFER_SIZE + SEARCH_BUFFER_SIZE) {
        //    cpy(from, to);
        //    return;
        //}
        
        var buffer := new byte[LOOKAHEAD_BUFFER_SIZE+SEARCH_BUFFER_SIZE];
        if !success || file_offset as int + buffer.Length as int > size as int {return;}
        var ok := fromFs.Read(file_offset as nat32, buffer, SEARCH_BUFFER_SIZE as int32, LOOKAHEAD_BUFFER_SIZE as int32);
        if !ok {return;}

        var insert: array<byte>;

        while file_offset as int + insert.Length as int <= size as int && ok && file_offset < size
            decreases size - file_offset
            //decreases size as int - (file_offset as int + insert.Length as int)
            //modifies fromFs
            //modifies env.ok;
            //modifies env.files;
            //invariant ok;
            //invariant fromFs.IsOpen();
            //invariant env.Valid();
            //invariant env.ok.ok();
        {
            insert := new byte[1];
            ok := fromFs.Read(file_offset as nat32, insert, 0 as int32, insert.Length as int32);
            file_offset := file_offset + 1;
            break;
        }

        /*while ok && file_offset < size
            decreases size - file_offset
            modifies fromFs
            modifies env.ok;
            modifies env.files;
            invariant fromFs.IsOpen();
            invariant env.Valid();
            invariant env.ok.ok();
        {
            if buffer == null {break;}
            if buffer.Length <= SEARCH_BUFFER_SIZE {return;}
            var match_, offset, len := FindBiguestMatch(buffer, SEARCH_BUFFER_SIZE);
            
            file_offset := file_offset + 1;

            if(!match_) {
                queueWord(1, buffer[SEARCH_BUFFER_SIZE]);
                insert := new byte[1];
            } else {
                queuePair(0, offset, len, buffer[SEARCH_BUFFER_SIZE]);
                insert := new byte[len];
            }
            
            if !ok || file_offset as int + insert.Length as int > size as int {break;}
            ok := fromFs.Read(file_offset as nat32, insert, 0 as int32, insert.Length as int32);
            buffer := ShiftInsert(buffer, insert);
        }*/
    }
}