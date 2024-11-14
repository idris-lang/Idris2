import fs from 'node:fs'
import tty from 'node:tty'
import { truncInt32 } from '../javascript/runtime.js'

export const prim__fileSize = fp => fs.fstatSync(fp.fd).size

export const prim__fileIsTTY = fp => Number(tty.isatty(fp.fd))

export function prim__filetime(file_ptr) {
  const { fd } = file_ptr
  const st = fs.fstatSync(fd)
  const ft = {
    atime_sec: truncInt32(Math.trunc(st.atimeMs / 1000)),
    atime_nsec: st.atimeMs * 1000000 % 1000000000,
    mtime_sec: truncInt32(Math.trunc(st.mtimeMs / 1000)),
    mtime_nsec: st.mtimeMs * 1000000 % 1000000000,
    ctime_sec: truncInt32(Math.trunc(st.ctimeMs / 1000)),
    ctime_nsec: st.mtimeMs * 1000000 % 1000000000
  };
  return ft
}
