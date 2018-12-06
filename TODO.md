TODO: QS
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

dafny/dafny assignment2/cp-basic/cp.dfy assignment2/cp-basic/IoNative.cs
dafny/dafny assignment2/cp-adv/cp.dfy assignment2/cp-adv/IoNative.cs
dafny/dafny assignment2/compression/compression.dfy assignment2/cp-adv/IoNative.cs
assignment2/compression/IoNative.cs

  if action[0] == '1' {
    LZSS.encode(from, to, env);
    print "Compress me!\n";
  } else if action[0] == '0' {
    LZSS.encode(from, to, env);
    print "Compress me!\n";
  } else {
    print "[USAGE]: mono compression.exe SrcFilename DstFilename!\n";
    return;
  }*/

O 3291648 - 3291648 - 3291648 - 3291648
C 5684277 - 3710680 - 4606370 - 3556747
            -w ignore 1