<?php get_header(); ?>

<div id="content-wrap">
  <div id="content">
    <div class="gap">
      <?php if (have_posts()) : ?>
      <h2 class="pagetitle">Zoekresultaten</h2>
      <?php while (have_posts()) : the_post(); ?>
      <div class="post" id="post-<?php the_ID(); ?>">
        <h2 class="post-title"><a class="intitle" href="<?php the_permalink() ?>" rel="bookmark" title="Permanente link naar <?php the_title(); ?>">
          <?php the_title(); ?>
          </a> <span class="commr">
          <?php comments_popup_link('0', '1', '%'); ?>
          </span></h2>
        <div class="timr"> Geplaatst op
          <?php the_time('F d, Y') ?>
          door
          <?php the_author() ?>
          <?php edit_post_link('e', '<span class="editr">[', '] </span>'); ?>
        </div>
        <div class="entry">
          <?php the_content('Lees de rest van dit bericht &rarr;'); ?>
        </div>
        <p class="postmetadata">
          <?php the_tags('Onderwerpen: ','','<br />');?>
<!--          <span class="catr">Category
          <?php the_category(', ') ?>
          </span> -->
        </p>
      </div>
      <?php endwhile; ?>
      <div class="navigation">
        <div class="alignleft">
          <?php next_posts_link('&larr; Vorige berichten') ?>
        </div>
        <div class="alignright">
          <?php previous_posts_link('Volgende berichten &rarr;') ?>
        </div>
      </div>
      <?php else : ?>
      <h2 class="center">Geen berichten gevonden. Nog een keer zoeken?</h2>
      <?php include (TEMPLATEPATH . '/searchform.php'); ?>
      <?php endif; ?>
</div> <!-- /gap -->
</div> <!-- /content -->
</div> <!-- /content-wrap -->
<?php get_sidebar(); ?>
<?php get_footer(); ?>
