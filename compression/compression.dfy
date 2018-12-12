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
  
  if act.Length != 1 {return;}
  var to, dstOk;
  if act[0] == '1' {
    to := LZSS.Encode(buffer);
    
    if 0 <= 0 as int <= 0 as int + |to| && -0x80000000 <= |to| < 0x80000000 {
      var toWrite := ArrayFromSeq(to);
      dstOk := dstFs.Write(0 as nat32, toWrite, 0, |to| as int32);
    }
    print "Compress me!\n";
  } else if act[0] == '0' {
    to := LZSS.Decode(buffer);
    if 0 <= 0 as int <= 0 as int + |to| && -0x80000000 <= |to| < 0x80000000 {
      var toWrite := ArrayFromSeq(to);
      dstOk := dstFs.Write(0 as nat32, toWrite, 0, |to| as int32);
    }
    print "Decompress me!\n";
  } else {
    print "[USAGE]: mono compression.exe {0=Compress,1=Decompress} SrcFilename DstFilename!\n";
  }
}