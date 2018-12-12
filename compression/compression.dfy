/*  
 * This is the skeleton for your compression and decompression routines.
 * As you can see, it doesn't do much at the moment.  See how much you 
 * can improve on the current algorithm! 
 *
 * Rui Maranhao -- rui@computer.org
 */

include "Io.dfy"
include "LZSS.dfy"

function compress(bytes:seq<byte>) : seq<byte>
{
  bytes
}

function decompress(bytes:seq<byte>) : seq<byte>
{
  bytes
}

lemma lossless(bytes:seq<byte>)
  ensures decompress(compress(bytes)) == bytes;
{
}

method compress_impl(bytes:array?<byte>) returns (compressed_bytes:array?<byte>)
  requires bytes != null;
  ensures  compressed_bytes != null;
  ensures  compressed_bytes[..] == compress(bytes[..]);
{
  compressed_bytes := bytes;
}

method decompress_impl(compressed_bytes:array?<byte>) returns (bytes:array?<byte>)
  requires compressed_bytes != null;
  ensures  bytes != null;
  ensures  bytes[..] == decompress(compressed_bytes[..]);
{
  bytes := compressed_bytes;
}

method ArrayFromSeq<A>(s: seq<A>) returns (a: array<A>)
  ensures a[..] == s
{
  a := new A[|s|] ( i requires 0 <= i < |s| => s[i] );
}

method {:main} Main(ghost env:HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok();
  modifies env.ok;
  modifies env.files;
{
  /*var alo := ArrayFromSeq([0,1,2,3,4,0,1,2]);
  var buffe: array<byte>, position: int := alo, 5;
  if 0 < position < buffe.Length {
    var match_: bool, offset: int, size: int := LZSS.LongestMatch(buffe, position);
    print(match_);
    print("\n");
    print(offset);
    print("\n");
    print(size);
    print("\n");
    return;
  }*/
  
  var argc := HostConstants.NumCommandLineArgs(env);

  if argc != 4 {
    print "[USAGE]: mono {0=Compress,1=Decompress} cp.exe SrcFilename DstFilename!\n";
    return;
  }
  
  var act := HostConstants.GetCommandLineArg(1, env);
  var src := HostConstants.GetCommandLineArg(2, env);
  var dst := HostConstants.GetCommandLineArg(3, env);

  var srcResult := FileStream.FileExists(src, env);
  if !srcResult {
    print "Source File Does Not Exist!\n";
    return;
  }
  
  var srcSuccess, srcFs := FileStream.Open(src, env);
  if !srcSuccess {
    print "Failed to open src file!\n";
    return;
  }

  var dstSuccess, dstFs := FileStream.Open(dst, env);
  if !dstSuccess {
    print "Failed to open dst file!\n";
    return;
  }

  var success, len: int32 := FileStream.FileLength(src, env);
  if !success {
    print "Couldn't get stream size!\n";
    return;
  }

  var buffer := new byte[len];
  var srcOk := srcFs.Read(0 as nat32, buffer, 0, len);
  if !srcOk {return;}
  
  var to: seq<byte> := LZSS.Encode(buffer);
  var toTmp := ArrayFromSeq(to);
  var to1: seq<byte> := LZSS.Decode(toTmp);
  
  var i := 0;
  while i < buffer.Length && i < |to1| && i < |to|
    decreases |to1| - i
  {
    if buffer[i] != to1[i] {
      print("(");
      print(i);
      print(",");
      print(buffer[i]);
      print(",");
      print(to[i]);
      print(",");
      print(to1[i]);
      print(")");
      print("\n");
      break;
    }
    i := i + 1;
  }
    print("\n");
    print("(");
    print(buffer.Length);
    print(",");
    print(|to|);
    print(",");
    print(|to1|);
    print(")\n");
  }
  /*if act.Length != 1 {return;}
  var to: array<byte>, toSize: int, dstOk;
  if act[0] == '1' {
    to, toSize := LZSS.Encode(buffer);
    
    /*var j := 0;
    while j < toSize <= to.Length
      decreases toSize - j
    {
      print(to[j]);
      j := j+1;
    }*

    if 0 <= 0 as int <= 0 as int + toSize as int <= to.Length && -0x80000000 <= toSize < 0x80000000 {
      dstOk := dstFs.Write(0 as nat32, to, 0, toSize as int32);
    }
    print "Compress me!\n";
  } else if act[0] == '0' {
    to, toSize := LZSS.Decode(buffer);
    if 0 <= 0 as int <= 0 as int + toSize as int <= to.Length && -0x80000000 <= toSize < 0x80000000 {
      dstOk := dstFs.Write(0 as nat32, to, 0, toSize as int32);
    }
    print "Decompress me!\n";
  } else {
    print "[USAGE]: mono compression.exe {0=Compress,1=Decompress} SrcFilename DstFilename!\n";
  }*/
}