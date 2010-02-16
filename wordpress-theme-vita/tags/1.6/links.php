<?php
/*
Template Name: Links
*/
?>
<?php get_header(); ?>

<div id="content-wrap">
  <div id="content">
    <div class="gap linkspage">
      <h2>Links:</h2>
      <div class="thelist">
        <ul>
          <?php get_links_list(); ?>
        </ul>
      </div>
</div> <!-- /gap -->
</div> <!-- /content -->
</div> <!-- /content-wrap -->
<?php get_sidebar(); ?>
<?php get_footer(); ?>
