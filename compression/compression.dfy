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
  /*var a: array<byte> := ArrayFromSeq([0]);
  var b: array<byte> := ArrayFromSeq([1, 2, 3, 4]);

  var c := LZSS.ShiftInsert(a, b);
  
  var i := 0;
  while i < c.Length
    decreases c.Length - i
  {
    print c[i];
    print "\n";
    i := i + 1;
  }*/

  /*var buffer: array<byte> := ArrayFromSeq([1, 2, 3, 4, 5, 1, 2, 3, 4]);

  var i := 0;
  while i < buffer.Length
    decreases buffer.Length - i
  {
    var ok:bool, bestOffsetSoFar: int, len: int := LZSS.FindBiguestMatch(buffer, i);
    print ok;
    print " - ";
    print bestOffsetSoFar;
    print " - ";
    print len;
    print "\n";
    i := i + 1;
  }*/

  var lzss: LZSS := new LZSS();

  var argc := HostConstants.NumCommandLineArgs(env);
  if argc != 3 {
    print "[USAGE]: mono compression.exe SrcFilename DstFilename!\n";
    return;
  }
  
  var from := HostConstants.GetCommandLineArg(1, env);
  var to := HostConstants.GetCommandLineArg(2, env);
  lzss.encode(from, to, env);

  print "Compress me!\n";
}