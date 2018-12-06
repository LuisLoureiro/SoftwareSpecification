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
  var argc := HostConstants.NumCommandLineArgs(env);
  if argc != 4 {
    print "[USAGE]: mono cp.exe SrcFilename DstFilename!\n";
    return;
  }
  
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
  /*var l := 0;
  while l < buffer.Length
    decreases buffer.Length - l
  {
    print(buffer[l]);
    print("-");
    l := l + 1;
  }
  print("\n");*/
  var to: array<byte>, toSize: int := LZSS.Encode(buffer);
  /*var i := 0;
  while i < toSize && i < to.Length
    decreases to.Length - i
  {
    print(to[i]);
    print("-");
    i := i + 1;
  }
  print("\n");*/
  
  if 0 < toSize < to.Length {
    var a := ArrayFromSeq(to[0..toSize]);
    var to1: array<byte>, toSize1: int := LZSS.Decode(a);
    if 0 < toSize1 < to1.Length {
      to1 := ArrayFromSeq(to1[0..toSize1]);
    }
    var i := 0;
    if buffer.Length != to1.Length {return;}
    
    while i < to1.Length
      decreases to1.Length - i
    {
      //print(to1[i]);
      //print("-");
      if buffer[i] != to1[i] {
        print("(");
        print(i);
        print(",");
        print(buffer[i]);
        print(",");
        print(to1[i]);
        print(")");
        print("\n");
      
        //break;
      }
      i := i + 1;
    }
    print("\n");
    print("(");
    print(buffer.Length);
    print(",");
    print(a.Length);
    print(",");
    print(to1.Length);
    print(")\n");

    var dstOk := dstFs.Write(0 as nat32, to1, 0, to1.Length as int32);
    //if dstOk {
    //  var a := dstFs.Close();
    //}
  }
}