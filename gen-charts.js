const { ChartJSNodeCanvas } = require('chartjs-node-canvas');

var results = require("./results.json");

var lang_color = {
  "agda": "pink",
  "haskell": "purple",
  "kind2": "gray",
};

var charts = {};
for (var result of results) {
  var chart = result[0] + "_" + result[1];
  var lang = result[2];
  var init = Number(result[3]);
  var time = Number(result[4]);

  if (!charts[chart]) {
    charts[chart] = {};
  }

  if (!charts[chart][lang]) {
    charts[chart][lang] = {
      label: lang,
      data: [],
      init: init,
      borderColor: lang_color[lang],
      fill: false,
    };
  }

  // FIXME: I'm replacing the first value by 0 since it is skewed.
  // Instead, we should perform a dry-run of the first benchmark.
  if (charts[chart][lang].data.length === 0) {
    charts[chart][lang].data.push(0);
  } else {
    charts[chart][lang].data.push(time);
  }
}

for (let chart in charts) {

  var max_time = 0;
  var labels = null;
  var datasets = [];
  for (var lang in charts[chart]) {
    datasets.push(charts[chart][lang]);
    for (var time of charts[chart][lang].data) {
      max_time = Math.max(max_time, time);
    }
    if (!labels) {
      labels = [];
      for (var i = 0; i < charts[chart][lang].data.length; ++i) {
        labels.push(String(charts[chart][lang].init + i));
      }
    }
  }


  const configuration = {
    type: 'line',
    data: {
      labels: labels,
      datasets: datasets
    },
    options: {
      responsive: true,
      plugins: {
        title: {
          display: true,
          text: chart,
        },
      },
      interaction: {
        intersect: false,
      },
      scales: {
        x: {
          display: true,
          title: {
            display: true
          }
        },
        y: {
          display: true,
          title: {
            display: true,
            text: 'Value'
          },
          suggestedMin: 0,
          suggestedMax: max_time,
        }
      }
    },
  };

  const width = 1200; //px
  const height = 400; //px
  const backgroundColour = 'white';
  const chartJSNodeCanvas = new ChartJSNodeCanvas({ width, height, backgroundColour });

  (async () => {
      const image = await chartJSNodeCanvas.renderToBuffer(configuration);
      require("fs").writeFileSync("image/"+chart+"_.png", image);
      //const dataUrl = await chartJSNodeCanvas.renderToDataURL(configuration);
      //const stream = chartJSNodeCanvas.renderToStream(configuration);
  })();
};
