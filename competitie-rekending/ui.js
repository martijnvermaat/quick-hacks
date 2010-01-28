$(document).ready(function() {


    var TO_POINTS = 0;
    var TO_PERFORMANCE = 1;
    var direction = TO_POINTS;

    var re_querystring = /^([^#?]*\??[^#]*)#?(.*)/;
    var location = window.location.href;

    var bookmarks = [];


    var calculate = function() {

        if (direction == TO_POINTS) {
            var points = calculator.points($('#events').val(),
                                           $('#male').is(':checked'),
                                           $('#performance').val());
            if (!isNaN(points))
                $('#points').val(points.toString());
        } else {
            $('#performance').val(
                calculator.performance($('#events').val(),
                                       $('#male').is(':checked'),
                                       $('#points').val()));
        }

        updateBookmark();

    };


    var toPoints = function() {
        direction = TO_POINTS;
        calculate();
    };


    var toPerformance = function() {
        direction = TO_PERFORMANCE;
        calculate();
    };


    var updateBookmark = function() {

        $('#bookmark').unbind('click');

        if (isNaN(parseInt($('#events').val()))
            || $('#points').val() == ''
            || $('#performance').val() == '') {

            $('#bookmark').bind('click', function() {
                return false;
            }).addClass('disabled');

        } else {

            $('#bookmark').click(function() {
                bookmark($('#events').val(),
                         $('#male').is(':checked'),
                         $('#performance').val(),
                         $('#points').val());
                return false;
            }).removeClass('disabled');

        }

    };


    var bookmark = function(event, sex, performance, points) {

        var hash = Math.floor(Math.random() * 100000000);

        bookmarks.push({'hash'        : hash,
                        'event'       : event,
                        'sex'         : sex,
                        'performance' : performance,
                        'points'      : points});

        var r = $('<a href="#" class="remove">Verwijder dit resultaat</a>');
        r.attr('title', r.text()).click(function() {
            bookmarks = $.grep(bookmarks, function(b, i) {
                return b.hash != hash;
            });
            $(this).parent().remove();
            updateLink();
            return false;
        });

        var s = $('#events option[value=' + event + ']').text();
        s += ' (' + (sex ? 'm' : 'v') + '): ';
        s += performance + ', ' + points;

        $('#bookmarks').append(
            $('<li>').text(s).prepend(r)
        );

        updateLink();

    };


    var updateLink = function() {

        $('#link').attr(
            'href',
            location.replace(re_querystring, '$1') + '#' +
                encodeURIComponent(JSON.stringify(bookmarks))
        );

        if (bookmarks.length > 0) {
            $('#bookmarks-title').show();
        } else {
            $('#bookmarks-title').hide();
        }

    };


    var loadBookmarks = function() {

        var s = decodeURIComponent(location.replace(re_querystring, '$2'));

        try {
            var p = JSON.parse(s);
            for (i = 0; i < p.length; i++) {
                bookmark(p[i].event, p[i].sex, p[i].performance, p[i].points);
            }
        } catch (e) {}

    };


    var ignoreNav = function(callback) {
        // Call callback if key was not <tab> or <shift>
        return function(e) {
            if (e.keyCode != 9 && e.keyCode != 0)
                callback(e);
        };
    };

    var bookmarkShortcut = function(e) {
        // Key 'b'
        if (e.which == 98 || e.which == 66) {
            e.preventDefault();
            e.stopPropagation();
            if (!$('#bookmark').hasClass('disabled'))
                $('#bookmark').click();
        }
    };


    var events = calculator.events();
    for (i = 0; i < events.length; i++)
        $('#events').append($('<option>').val(i).text(events[i]));

    $('#events').bind('change keyup', calculate);

    $('#male, #female').click(calculate);

    $('#performance').keyup(ignoreNav(toPoints));
    $('#points').keyup(ignoreNav(toPerformance));

    $(document).keypress(bookmarkShortcut);

    updateLink();
    updateBookmark();
    loadBookmarks();


});
