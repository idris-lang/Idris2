import fs from 'node:fs'
import { parseMode } from './utils.js'

export const prim__close = (fp) => fs.closeSync(fp.fd)

export function prim__open(n, m) {
  try {
    const fd = fs.openSync(n, parseMode(m))
    return { fd: fd, buffer: Buffer.alloc(0), name: n, eof: false }
  } catch (e) {
    process.__lasterr = e
    return null
  }
}
