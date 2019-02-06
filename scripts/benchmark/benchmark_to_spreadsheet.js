#!/usr/bin/env node
let program = require('commander');

program
    .arguments('<jsonFile>')
    .action(function (jsonFile) {
        let lineReader = require('readline').createInterface({
            input: require('fs').createReadStream(jsonFile)
        });
        console.log("class file; function name; execution time (ms);"
        + "success; goals covered; total number of goals");
        lineReader.on('line', function (data) {
            let json = JSON.parse(data.toString());
            console.log(
                json.classFile +";" +
                json['function'].replace(/;/g, "_") + "; " +
                json.execTime + ";" +
                json.success + ";" +
                ((typeof json.goals != 'undefined')? json.goals.goalsCovered : "0") + ";" +
                ((typeof json.goals != 'undefined')? json.goals.totalGoals : ""));
        });
    })
    .parse(process.argv);
