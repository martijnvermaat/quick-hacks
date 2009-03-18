<?php
/*
Template Name: Archives
*/
?>
<?php get_header(); ?>

<div id="content-wrap">
  <div id="content">
    <div class="gap archives post">
      <div class="arlist clearfix">
        <h2>Archieven</h2>
        <h3>Per maand:</h3>
        <ul>
          <?php wp_get_archives('type=monthly&show_post_count=1') ?>
        </ul>
      </div>
<!--      <div class="arlist clearfix">
        <h3>Per categorie:</h3>
        <ul>
          <?php wp_list_categories('title_li=&hierarchical=0&show_count=1') ?>
        </ul>
      </div> -->
      <?php if (function_exists('wp_tag_cloud')) { ?>
      <div id="archivebox">
        <h3>Per onderwerp:</h3>
        <ul class="list1">
          <?php wp_tag_cloud('smallest=10&largest=18'); ?>
        </ul>
      </div>
      <!--/archivebox-->
      <?php } ?>
</div> <!-- /gap -->
</div> <!-- /content -->
</div> <!-- /content-wrap -->
<?php get_sidebar(); ?>
<?php get_footer(); ?>
