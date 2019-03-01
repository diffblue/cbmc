#!/usr/bin/env node
let program = require('commander');

program
    .arguments('<jsonFile>')
    .option('-t, --total', 'Only print the total time')
    .action(function (jsonFile) {
        let lineReader = require('readline').createInterface({
            input: require('fs').createReadStream(jsonFile)
        });
        const printTotalTime = typeof program.total != 'undefined';
        let totalTime = 0.0;
        if (!printTotalTime)
            console.log("class file; function name; execution time (ms);"
                        + "success; goals covered; total number of goals");
        lineReader.on('line', function (data) {
            let json = JSON.parse(data.toString());
            totalTime += parseFloat(json.execTime);
            if (printTotalTime)
                return;
            console.log(
                json.classFile +";" +
                json['function'].replace(/;/g, "_") + "; " +
                json.execTime + ";" +
                json.success + ";" +
                ((typeof json.goals != 'undefined')? json.goals.goalsCovered : "0") + ";" +
                ((typeof json.goals != 'undefined')? json.goals.totalGoals : ""));
        });
        if (printTotalTime) {
            lineReader.on('close', function () {
                console.log(jsonFile + "; " + totalTime)
            });
        }
    })
    .parse(process.argv);
