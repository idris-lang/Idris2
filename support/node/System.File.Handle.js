import fs from 'node:fs'

export const prim__close = (fp) => fs.closeSync(fp.fd)
