function printTime(seconds, hourSuffix, minuteSuffix, secSuffix) {
    hourSuffix   = (hourSuffix == undefined)   ? ":" : hourSuffix;
    minuteSuffix = (minuteSuffix == undefined) ? ":" : minuteSuffix;
    secSuffix    = (secSuffix == undefined)    ? ""  : secSuffix;

    var hours = Math.floor(seconds / 3600);
    var mins  = Math.floor( (seconds - hours * 3600) / 60 );
    var secs  = seconds - mins * 60 - hours * 3600;

    if (hours < 10) hours = "0" + hours;
    if (mins  < 10) mins  = "0" + mins;
    if (secs  < 10) secs  = "0" + secs;

    var res = hours + hourSuffix + mins + minuteSuffix + secs + secSuffix;

    return res;
}

/**
 * Starts a new counter
 * startTime: the start time in milliseconds
 * setTime: the function we have to call that will print the time. Requires one argument: the current time in milliseconds
 * interval: number of milliseconds we have to wait
 * onTimerFinished: function without arguments, that is called when the timer reaches 0
 */
 var counters = [];
 var next_counter = 0;
function startCounter(startTime, printTime, interval, onTimerFinished) {
    interval = (interval == undefined) ? 1000 : interval;

    var curr_counter = next_counter;
    counters[curr_counter] =
        {
            time: startTime,
            counter: setInterval(function() {
                counters[curr_counter].time -= interval;

                if (counters[curr_counter].time <= 0) {
                    clearInterval(counters[curr_counter].counter);
                    if (onTimerFinished != undefined)
                        onTimerFinished();

                    return;
                }

                printTime(counters[curr_counter].time);
            }, interval)
        };

    printTime(counters[curr_counter].time);
    next_counter++;
}