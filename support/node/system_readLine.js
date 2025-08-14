import fs from 'node:fs'

// System.File.prim__readLine
export function prim__readLine(file_ptr) {
  const LF = 0x0a
  const readBuf = Buffer.alloc(1)
  let lineEnd = file_ptr.buffer.indexOf(LF)
  while (lineEnd === -1) {
    const bytesRead = fs.readSync(file_ptr.fd, readBuf, 0, 1, null)
    if (bytesRead === 0) {
      file_ptr.eof = true
      const line = file_ptr.buffer.toString('utf-8')
      file_ptr.buffer = Buffer.alloc(0)
      return line
    }
    file_ptr.buffer = Buffer.concat([file_ptr.buffer, readBuf.slice(0, bytesRead)])
    lineEnd = file_ptr.buffer.indexOf(LF)
  }
  const line = file_ptr.buffer.slice(0, lineEnd + 1).toString('utf-8')
  file_ptr.buffer = file_ptr.buffer.slice(lineEnd + 1)
  return line
}

// Prelude.prim__getStr
export function prim__getStr() {
  return prim__readLine({
    fd: 0,
    buffer: Buffer.alloc(0),
    name: "<stdin>",
    eof: false,
  });
}
