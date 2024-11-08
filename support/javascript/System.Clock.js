const clock_process_start_time = performance.now();

export function prim__clockTimeProcess() {
    return performance.now() - clock_process_start_time
}

export function prim__clockTimeThread() {
    // The JS backend currently doesn't support threads
    // This may be possible with the WebWorkers api, if so change this implementation
    return performance.now() - clock_process_start_time
}
