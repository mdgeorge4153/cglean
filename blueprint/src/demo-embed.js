// \demo{path} (web-macros.tex) renders as a link to the demo, which is copied
// into the published site under demo/ (.github/workflows/blueprint.yml).
// Replace each such link with the demo itself, keeping the link below it to
// open the demo on its own. The demo is on the same site, so its height can be
// read directly: the frame follows it (e.g. as results appear), and never
// needs scrollbars.
$(function () {
  $('a[href^="demo/"]').each(function () {
    var $link = $(this);
    var $frame = $('<iframe class="demo" loading="lazy" scrolling="no"></iframe>')
      .attr('src', $link.attr('href'))
      .attr('title', 'Demo');
    $frame.on('load', function () {
      var doc = this.contentDocument;
      if (!doc) return;
      var fit = function () { $frame.height(doc.documentElement.scrollHeight); };
      new ResizeObserver(fit).observe(doc.body);
      fit();
    });
    $link.before($frame);
    $link.text('Open the demo on its own page');
  });
});
