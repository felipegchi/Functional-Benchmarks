var fs = require("fs");
var exec_sync = require("child_process").execSync;

var SMALL = false;

var langs = {

  haskell: {
    runtime: {
      run: true,
      tasks: {
        list_fold: [1,64],
        tree_fold: [26,32],
      },
      build: (task) => {
        save("main.hs", load("Runtime/"+task+".hs"));
        exec("ghc -O2 main.hs -o main.bin");
      },
      bench: (task, size) => {
        return bench("./main.bin " + size);
      },
      clean: () => {
        rm("main.hs");
        rm("main.hi");
        rm("main.o");
        rm("main.bin");
      },
    }
  },

  kind2: {
    runtime: {
      run: true,
      tasks: {
        list_fold: [1,64],
        tree_fold: [26,32],
      },
      build: (task) => {
        save("main.kind2", load("Runtime/"+task+".kind2"));
        exec("kind2 to-hvm main.kind2 >> main.hvm");
        exec("hvm compile main.hvm");
        exec("clang -O2 main.c -o main.bin");
      },
      bench: (task, size) => {
        return bench("./main.bin " + size + " 2>/dev/null");
      },
      clean: () => {
        rm("main.kind2");
        rm("main.c");
        rm("main.hvm");
        rm("main.bin");
      },
    },
    checker: {
      run: true,
      tasks: {
        nat_exp: [10,14],
        nat_exp_church: [16,24],
        tree_fold: [16,24],
        tree_fold_church: [16,24],
      },
      build: (task) => {
        save("Base.kind2", load("Checker/Base.kind2"));
      },
      bench: (task, size) => {
        var code = load("Checker/"+task+".kind2");
        code = code.replace("Size = Base.N1", "Size = Base.N" + size);
        code = code.replace("Size = Base.Church.N1", "Size = Base.Church.N" + size);
        code = repeat(code, "//REPEAT", 2 ** size);
        save("main.kind2", code);
        exec("kind2 gen-checker main.kind2");
        return bench("hvm --memory-size 12G run main.check.hvm 2>/dev/null");
      },
      clean: (task) => {
        rm("Base.kind2");
        rm("main.kind2");
        rm("main.check.hvm");
      },
    }
  },

  agda: {
    checker: {
      run: true,
      tasks: {
        nat_exp: [10,14],
        nat_exp_church: [16,24],
        tree_fold: [16,24],
        tree_fold_church: [16,24],
      },
      build: (task) => {
        save("Base.agda", load("Checker/Base.agda"));
      },
      bench: (task, size) => {
        var code = load("Checker/"+task+".agda");
        code = code.replace("Size = Base.N1", "Size = Base.N" + size);
        code = code.replace("Size = Base.Church-N1", "Size = Base.Church-N" + size);
        code = repeat(code, "--REPEAT", 2 ** size);
        save("main.agda", code);
        return bench("agda -i src main.agda");
      },
      clean: () => {
        rm("main.agda");
        rm("Base.agda");
        rm("main.agdai");
        rm("Base.agdai");
      },
    }
  },

};

for (var name in langs) {
  for (var kind in langs[name]) {
    langs[name][kind].clean();
  }
}

var results = [];

for (var lang in langs) {
  for (var kind in langs[lang]) {
    for (var task in langs[lang][kind].tasks) {
      if (langs[lang][kind].run) {
        langs[lang][kind].clean(task);
        langs[lang][kind].build(task);
        var min_size = langs[lang][kind].tasks[task][0];
        var max_size = SMALL ? min_size + 2 : langs[lang][kind].tasks[task][1];
        for (var size = min_size; size <= max_size; ++size) {
          if (size === min_size) {
            langs[lang][kind].bench(task, size); // dry-run to heat up
          }
          var time = langs[lang][kind].bench(task, size);
          results.push([kind, task, lang, size, time]);
          console.log(kind + " | " + task + " | " + lang + " | " + size + " | " + time.toFixed(3) + "s");
        }
        langs[lang][kind].clean(task);
      }
    }
  }
}

fs.writeFileSync("./results.json", JSON.stringify(results, null, 2));

function exec(str) {
  try {
    return exec_sync(str).toString();
  } catch (e) {
    console.log(e.stdout.toString());
    console.log(e.stderr.toString());
    process.exit();
  }
}

function load(name) {
  return fs.readFileSync(name, "utf8");
}

function save(name, text) {
  fs.writeFileSync(name, text);
}

function rm(name) {
  if (fs.existsSync(name)) {
    fs.unlinkSync(name);
  }
}

function repeat(code, label, size) {
  var new_code = "";
  for (var line of code.split("\n")) {
    var times = line.indexOf("--REPEAT") !== -1 ? size : 1;
    for (var i = 0; i < times; ++i) {
      new_code = new_code + line + "\n";
    }
  }
  return new_code;
}

function bench(cmd) {
  var ini = Date.now();
  var res = exec(cmd, {skipThrow: 1}).toString().replace(/\n/g,"");
  //console.log(">> done: " + res);
  var end = Date.now();
  return (end - ini) / 1000;
}

