<form method="get" id="searchform" action="<?php bloginfo('home'); ?>/">
  <div>
    <?php
$value = wp_specialchars($s, 1);
if (!$value) {
$value = 'To Search, just type and enter';
}
?>
    <input type="text" value="<?php echo $value; ?>" name="s" id="s" onfocus="if (this.value == 'To Search, just type and enter') {this.value = '';}" onblur="if (this.value == '') {this.value = 'To Search, just type and enter';}" />
    <input type="submit" id="searchsubmit" value="Search" />
  </div>
</form>
