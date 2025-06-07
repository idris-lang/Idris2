import fs from "node:fs";

export function prim__getChar() {
  const readBuf = Buffer.alloc(1);
  if (fs.readSync(process.stdin.fd, readBuf, 0, 1) === 0) {
    // No bytes read, getChar from libc returns -1 in this case.
    return String.fromCharCode(-1);
  } else {
    return readBuf.toString("utf-8");
  }
}
