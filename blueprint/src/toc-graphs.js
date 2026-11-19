// plastexdepgraph (dep_by=chapter) lists every "Chapter N graph" link at the
// bottom of the sidebar. Move each one to the top of chapter N's entry, as
// "Dependency graph", giving the chapter a collapsible sub-list (as the theme
// does for chapters with sections) if it doesn't have one. (The graph pages
// themselves have no sidebar.)
$(function () {
  var $toc = $("nav.toc > ul.sub-toc-0");
  $toc.children("li").each(function () {
    var $item = $(this);
    var m = ($item.children("a").attr("href") || "")
      .match(/^dep_graph_chapter_(\d+)\.html$/);
    if (!m) return;
    var $chapter = $toc.children("li").filter(function () {
      return $(this).find("> a > span.toc_ref").text() === m[1];
    });
    if (!$chapter.length) return;
    var $sub = $chapter.children("ul");
    if (!$sub.length) {
      $chapter.append(' <span class="expand-toc">▶</span>');
      $sub = $('<ul class="sub-toc-1"></ul>').appendTo($chapter);
    }
    $item.children("a").text("Dependency graph");
    $item.prependTo($sub);
  });
});
