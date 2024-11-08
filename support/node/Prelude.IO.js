import fs from 'node:fs';
import { prim__readLine } from './System.File.ReadWrite.js'

// NOTE: will not create cycle, bc this will be compiled as './support.js' file
export function prim__getStr() {
  return prim__readLine({ fd: 0, buffer: Buffer.alloc(0), name: '<stdin>', eof: false })
}

export function prim__getChar() {
  const readBuf = Buffer.alloc(1);
  if (fs.readSync(process.stdin.fd, readBuf, 0, 1) === 0) {
    // No bytes read, getChar from libc returns -1 in this case.
    return String.fromCharCode(-1)
  } else {
    return readBuf.toString('utf-8')
  }
}
