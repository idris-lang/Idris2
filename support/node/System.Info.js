import os from 'node:os'

export const prim__getNProcessors = () => os.cpus().length
