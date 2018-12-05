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

  var success, len: int32 := FileStream.FileLength(src, env);
  if !success {
    print "Couldn't get stream size!\n";
    return;
  }

  var buffer := new byte[len];
  var srcOk := srcFs.Read(0 as nat32, buffer, 0, len);
  var l := 0;
  while l < buffer.Length
    decreases buffer.Length - l
  {
    print(buffer[l]);
    print("-");
    l := l + 1;
  }
  print("\n");
  var to: array<byte>, toSize: int := LZSS.Encode(buffer);
  var i := 0;
  while i < toSize && i < to.Length
    decreases to.Length - i
  {
    print(to[i]);
    print("-");
    i := i + 1;
  }
  print("\n");
  
  if 0 < toSize < to.Length {
    var a := ArrayFromSeq(to[0..toSize]);
    var to1: array<byte>, toSize1: int := LZSS.Decode(a);
    var i := 0;
    while i < to1.Length
      decreases to1.Length - i
    {
      print(to1[i]);
      print("-");
      i := i +1;
    }
    print("\n");
  }
}