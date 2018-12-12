/*
 * This is the skeleton for your cp utility.
 *
 * Rui Maranhao -- rui@computer.org
 */

include "Io.dfy"

// Useful to convert Dafny strings into arrays of characters.
method ArrayFromSeq<A>(s: seq<A>) returns (a: array<A>)
  ensures a[..] == s
{
  a := new A[|s|] ( i requires 0 <= i < |s| => s[i] );
}
method {:main} Main(ghost env: HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok()
  requires |env.constants.CommandLineArgs()| == 3
  modifies env.ok
  modifies env.files
{
  var argc := HostConstants.NumCommandLineArgs(env);
  if argc != 3 {
    print "[USAGE]: mono cp.exe SrcFilename DstFilename!\n";
    return;
  }
  
  var src := HostConstants.GetCommandLineArg(1, env);
  var dst := HostConstants.GetCommandLineArg(2, env);

  var srcResult := FileStream.FileExists(src, env);
  var dstResult := FileStream.FileExists(dst, env);
  if !srcResult {
    print "Source File Does Not Exist!\n";
    return;
  }
  if dstResult {
    print "Destiny File Already Exist!\n";
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
  var dstOk := dstFs.Write(0 as nat32, buffer, 0, len);

  if !dstOk {return;}
  var bufferDst := new byte[len];
  dstOk := dstFs.Read(0 as nat32, bufferDst, 0, len);
  
  if !dstOk {return;}
  var ok := srcFs.Close();
  if !ok {return;}
  ok := dstFs.Close();
  print "Done!\n";
}