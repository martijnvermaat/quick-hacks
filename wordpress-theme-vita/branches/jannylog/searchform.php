<form method="get" id="searchform" action="<?php bloginfo('home'); ?>/">
  <div>
    <?php
$value = wp_specialchars($s, 1);
if (!$value) {
$value = 'Doorzoek de site...';
}
?>
    <input type="text" value="<?php echo $value; ?>" name="s" id="s" onfocus="if (this.value == 'Doorzoek de site...') {this.value = '';}" onblur="if (this.value == '') {this.value = 'Doorzoek de site...';}" />
    <input type="submit" id="searchsubmit" value="Zoeken" />
  </div>
</form>
