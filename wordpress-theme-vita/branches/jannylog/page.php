<?php get_header(); ?>

<div id="content-wrap">
  <div id="content">
    <div class="gap">
      <?php if (have_posts()) : while (have_posts()) : the_post(); ?>
      <div class="post" id="post-<?php the_ID(); ?>">
        <h2>
          <?php the_title(); ?>
        </h2>
        <div class="entry">
          <?php the_content('<p class="serif">Lees de rest van de pagina &raquo;</p>'); ?>
          <?php wp_link_pages(array('before' => '<p><strong>Pagina's:</strong> ', 'after' => '</p>', 'next_or_number' => 'number')); ?>
        </div>
      </div>

      <?php comments_template(); ?>

      <?php endwhile; endif; ?>
      <?php edit_post_link('Bewerk deze pagina.', '<p>', '</p>'); ?>
</div> <!-- /gap -->
</div> <!-- /content -->
</div> <!-- /content-wrap -->
<?php get_sidebar(); ?>
<?php get_footer(); ?>
