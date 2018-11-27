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
  var ok := srcFs.Close();
  if !ok {return;}
  ok := dstFs.Close();
  print "Done!\n";
}
/*lemma ReadLemma(fs: FileStream, file_offset: nat32, buffer: array?<byte>, num_bytes: int32)
  ensures fs.env.Valid();
  ensures fs.env.ok.ok();
  ensures fs.IsOpen();
  ensures fs.Name() in fs.env.files.state();
  ensures file_offset as int + num_bytes as int <= |fs.env.files.state()[fs.Name()]|;
  ensures fresh(buffer);
{
  assume false;
}

while file_offset as int + BYTES_TO_READ as int < len as int
    decreases len as int - (file_offset as int + BYTES_TO_READ as int);
  {
    ReadLemma(srcFs, file_offset as nat32, buffer, BYTES_TO_READ);
    srcOk := srcFs.Read(file_offset as nat32, buffer, start, BYTES_TO_READ);
    dstOk := dstFs.Write(file_offset as nat32, buffer, start, BYTES_TO_READ);
    file_offset := file_offset + BYTES_TO_READ;
  }
*/