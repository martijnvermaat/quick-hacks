<div class="side1">
  <ul>
    <?php J_ShowAbout(); ?>
    <li class="search boxr clearfix">
      <?php include (TEMPLATEPATH . '/searchform.php'); ?>
    </li>
    <?php J_ShowRecentPosts();?>
    <?php if ( function_exists('dynamic_sidebar') && dynamic_sidebar(1) ) : else : ?>
    <li class="boxr caty clearfix">
      <h2>Archieven</h2>
      <ul>
        <?php wp_get_archives('type=monthly'); ?>
      </ul>
    </li>
    <li class="boxr caty clearfix">
      <h3>Onderwerpen</h3>
      <ul>
        <?php wp_tag_cloud('smallest=10&largest=18'); ?>
      </ul>
    </li>
<!--    <li class="boxr caty clearfix">
      <h3>Categories</h3>
      <ul>
        <?php wp_list_categories('show_count=0&title_li='); ?>
      </ul>
    </li>
!-->
    <?php endif; // End of Sidebar ?>
  </ul>
</div>
<div class="side2">
<div class="gapy">
<ul>
<?php if ( function_exists('dynamic_sidebar') && dynamic_sidebar(2) ) : else : ?>
<?php wp_list_bookmarks('orderby=order&category_orderby=order'); ?>
<li class="boxr">
  <h2>Meta</h2>
  <ul>
    <?php wp_register(); ?>
    <li>
      <?php wp_loginout(); ?>
    </li>
    <li><a href="http://wordpress.org/" title="Powered by WordPress, state-of-the-art semantic personal publishing platform.">WordPress</a></li>
    <?php wp_meta(); ?>
  </ul>
</li>
<?php endif; // End of Sidebar ?>
</div>
</div>
