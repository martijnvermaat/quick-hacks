<div class="side1">
  <ul>
    <?php J_ShowAbout(); ?>
    <li class="search boxr clearfix">
      <?php include (TEMPLATEPATH . '/searchform.php'); ?>
    </li>
    <?php J_ShowRecentPosts();?>
    <?php if ( function_exists('dynamic_sidebar') && dynamic_sidebar(1) ) : else : ?>
    <li class="boxr caty clearfix">
      <h2>Archives</h2>
      <ul>
        <?php wp_get_archives('type=monthly'); ?>
      </ul>
    </li>
    <li class="boxr caty clearfix">
      <h3>Categories</h3>
      <ul>
        <?php wp_list_categories('show_count=0&title_li='); ?>
      </ul>
    </li>
    <?php endif; // End of Sidebar ?>
  </ul>
</div>
<div class="side2">
<div class="gapy">
<ul>
<?php if ( function_exists('dynamic_sidebar') && dynamic_sidebar(2) ) : else : ?>
<?php wp_list_bookmarks(); ?>
<li class="boxr">
  <h2>Meta</h2>
  <ul>
    <?php wp_register(); ?>
    <li>
      <?php wp_loginout(); ?>
    </li>
    <li><a href="http://validator.w3.org/check/referer" title="This page validates as XHTML 1.0 Transitional">Valid <abbr title="eXtensible HyperText Markup Language">XHTML</abbr></a></li>
    <li><a href="http://gmpg.org/xfn/"><abbr title="XHTML Friends Network">XFN</abbr></a></li>
    <li><a href="http://wordpress.org/" title="Powered by WordPress, state-of-the-art semantic personal publishing platform.">WordPress</a></li>
    <?php wp_meta(); ?>
  </ul>
</li>
<?php endif; // End of Sidebar ?>
</div>
</div>
