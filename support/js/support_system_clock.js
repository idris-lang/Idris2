const support_system_clock_process_start_time = performance.now();

function support_system_clock_clockTimeProcess() {
    return performance.now() - support_system_clock_process_start_time
}

function support_system_clock_clockTimeThread() {
    // The JS backend currently doesn't support threads
    // This may be possible with the WebWorkers api, if so change this implementation
    return performance.now() - support_system_clock_process_start_time
}
