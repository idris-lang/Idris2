const support_system_file_fs = require("fs")

function support_system_file_readLine(file_ptr){
  const LF = 0x0a;
  const readBuf = Buffer.alloc(1);
  let lineEnd = file_ptr.buffer.indexOf(LF);
  while (lineEnd === -1) {
    const bytesRead = support_system_file_fs.readSync(file_ptr.fd, readBuf,0,1,null);
    if (bytesRead === 0) {
      file_ptr.eof = true;
      const line = file_ptr.buffer.toString('utf-8');
      file_ptr.buffer = Buffer.alloc(0)
      return line
    }
    file_ptr.buffer = Buffer.concat([file_ptr.buffer, readBuf.slice(0, bytesRead)]);
    lineEnd = file_ptr.buffer.indexOf(LF);
  }
  const line = file_ptr.buffer.slice(0, lineEnd + 1).toString('utf-8');
  file_ptr.buffer = file_ptr.buffer.slice(lineEnd + 1);
  return line;
}


function support_system_file_getStr(){
  return support_system_file_readLine({fd:0, buffer: Buffer.alloc(0), name:'<stdin>', eof: false})
}

function support_system_file_openFile(n,m){
  try{
    const fd = support_system_file_fs.openSync(n, m)
    return {fd: fd, buffer: Buffer.alloc(0), name:n, eof: false}
  }catch(e){
    process.__lasterr = e; return null
  }
}


function support_system_file_chmod(filename, mode){
  try{
    support_system_file_fs.chmodSync(filename, Number(mode))
    return 0n
  }catch(e){
    process.__lasterr = e;
    return 1n
  }
}
