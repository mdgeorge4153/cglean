// \demo{path} (web-macros.tex) renders as a link to the demo, which is copied
// into the published site under demo/ (.github/workflows/blueprint.yml).
// Replace each such link with the demo itself, keeping the link below it to
// open the demo on its own.
$(function () {
  $('a[href^="demo/"]').each(function () {
    var $link = $(this);
    var $frame = $('<iframe class="demo" loading="lazy"></iframe>')
      .attr('src', $link.attr('href'))
      .attr('title', 'Demo');
    $link.before($frame);
    $link.text('Open the demo on its own page');
  });
});
