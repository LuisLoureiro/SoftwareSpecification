TODO: QS
    verify override for smaller files
    basic
        cp.dfy
    adv
        prove that this is the only time when you will overwrite an existing file
        cp.dfy
        Io.dfy
            HostConstants.ReadLine
    compression
        Io.dfy
            HostConstants.ReadLine
        In your file, you should prove that calling decompress on compress is the identity function
        Be sure to document any references you use for your compression algorithms.

/*
invariant srcOk;
invariant dstOk;
invariant env.Valid();
invariant env.ok.ok();
invariant srcFs.IsOpen();
invariant dstFs.IsOpen();

if !dstOk {return;}

var closed := srcFs.Close();                     //TODO: REMOVE VAR??????
if !closed {return;}
var _ := dstFs.Close();                          //TODO: REMOVE VAR??????

print "Done!\n";
*/

dafny/dafny assignment2/cp-basic/cp.dfy assignment2/cp-basic/Io.dfy assignment2/cp-basic/IoNative.cs
dafny/dafny assignment2/cp-adv/cp.dfy assignment2/cp-adv/Io.dfy assignment2/cp-adv/IoNative.cs
dafny/dafny assignment2/compression/compression.dfy assignment2/compression/Io.dfy assignment2/compression/IoNative.cs