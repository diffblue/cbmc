#!/usr/bin/env node

let program = require('commander');
let execFileSync = require('child_process').execFileSync;
let fs = require('fs');

// Parse options and launch jbmc
program
    .arguments('<executable>')
    .description("This script can run an executable like JBMC on a list of Java methods in "
        + "a  maven project. It must be run from the target/classes directory of a Java project to analyze. "
        + "It outputs information in the Json format.")
    .option('-m, --models <model-path>', 'Path to the models library')
    .option('-a, --arguments <json file>', 'Path to a json file describing arguments to give the executable')
    .option('-l, --method-list <text file>', 'Text file from which to read the methods to analyze')
    .option('-s, --stop-after-symex', 'Only perform symex and do not run the solver')
    .option('-p, --show-properties', 'Only show the number of goals in the function')
    .action(function (executable) {
        if (typeof program.methodList === 'undefined')
            throw new Error('method list argument is required');
        if (typeof executable === 'undefined')
            throw new Error('executable argument is required');
        runOnFunctionList(executable, program.models, program.arguments,
            program.methodList,
            typeof program.stopAfterSymex !== 'undefined',
            typeof program.showProperties !== 'undefined');
    })
    .parse(process.argv);

/// Convert the args to an argument array
function argsToArray(args) {
    let result = [];
    const keys = Object.keys(args);
    for (let i = 0; i < keys.length; i++) {
        if (typeof args[keys[i]] === "boolean") {
            if (args[keys[i]])
                result.push(`--${keys[i]}`);
        }
        else if (Array.isArray(args[keys[i]])) {
            for (let j = 0; j < args[keys[i]].length; j++) {
                result.push(`--${keys[i]}`);
                result.push(`${args[keys[i]][j]}`);
            }
        }
        else {
            result.push(`--${keys[i]}`);
            result.push(`${args[keys[i]]}`);
        }
    }
    return result;
}

function arrayToString(args) {
    let result = "";
    for(let i = 0; i < args.length; i++) {
        result = result + args[i] + " ";
    }
    return result
}

/// Get the coverage info from the json output if available
function readCoverageInfo(stdout) {
    const jsonOutput = JSON.parse(stdout);
    for (let i = 0; i < jsonOutput.length; i++) {
        if (typeof jsonOutput[i].goalsCovered !== 'undefined')
            return { goalsCovered: jsonOutput[i].goalsCovered, totalGoals: jsonOutput[i].totalGoals }
    }
}

/// Get the number of reachability goals from the json output
function readNumberOfGoals(stdout) {
    const jsonOutput = JSON.parse(stdout);
    for (let i = 0; i < jsonOutput.length; i++) {
        if (typeof jsonOutput[i].properties !== 'undefined')
            return jsonOutput[i].properties.length - 1;
    }
    return 0;
}
function readJsonFile(fileName) {
    return JSON.parse(fs.readFileSync(fileName, 'utf8'));
}

/// Read the options from tools.json and launch the executable
function run(executable, modelsPath, argumentsFile, functionName,
    classFile, stopAfterSymex, showProperties) {
    const config = readJsonFile(
        argumentsFile || "benchmark_java_arguments.json");

    if (typeof functionName !== 'undefined')
        config['function'] = functionName;
    if (showProperties) {
        config['show-properties'] = true;
    }
    else {
        if (typeof modelsPath !== 'undefined')
            config.classpath = `${modelsPath}:${config.classpath}`;
        if (stopAfterSymex) {
            config['show-vcc'] = true;
            config['json-ui'] = false;
            config.verbosity = 0;
        }
    }
    // timeout isn't a jbmc option but only used by this script
    const timeout = config.timeout;
    config['timeout'] = false;
    let command = [executable, classFile, ...argsToArray(config)];
    const startTime = new Date();
    try {
        const wrapper = __dirname + "/process_wrapper.sh";
        const output = execFileSync(wrapper, command, { timeout: 1000 * timeout }).toString();
        let execTime = fs.readFileSync('tmp_time.out', 'utf8').split('\n')[0];
        let result = {
            classFile: classFile, function: functionName,
            execTime: execTime, success: true,
            commandLine: arrayToString(command)
        }
        if (showProperties) {
            result.goals = readNumberOfGoals(output);
        } else if (!stopAfterSymex) {
            result.goals = readCoverageInfo(output)
        }
        return JSON.stringify(result);
    } catch (err) {
        return JSON.stringify({
            classFile: classFile, function: functionName,
            execTime: (new Date() - startTime) / 1000, success: false,
            commandLine: arrayToString(command)
        });
    }
}

function runOnFunctionList(
    executable, modelsPath, toolsPath, methodList, stopAfterSymex, showProperties) {
    let lineReader = require('readline').createInterface({
        input: require('fs').createReadStream(methodList)
    });
    lineReader.on('line', function (data) {
        const methodSignature = data.toString();
        const methodName = methodSignature.substring(0, methodSignature.indexOf(':'));
        const classFileName = methodName.substring(0, methodName.lastIndexOf('.')).replace(/\./g, '/') + ".class";
        console.log(run(executable, modelsPath, toolsPath,
            methodSignature, classFileName, stopAfterSymex, showProperties));
    });
}
