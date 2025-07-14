import fs from 'node:fs'

export const prim__readBufferData = (f, b, l, m) => fs.readSync(f.fd, b, l, m)
export const prim__writeBufferData = (f, b, l, m) => fs.writeSync(f.fd, b, l, m)
