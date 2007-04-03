// ==UserScript==
// @name          Nu Compact
// @namespace     http://www.cs.vu.nl/~mvermaat/
// @description   Remove pictures from frontpage stories keeping just links
// @include       http://www.nu.nl/
// ==/UserScript==


/*
    Nu Compact

    Version: 0.2.1, 2007-04-03

    http://www.cs.vu.nl/~mvermaat/greasemonkey

    Martijn Vermaat, mvermaat@cs.vu.nl


    Pictures added to stories on nu.nl have nothing to do with
    the stories most of the time. They occupy a lot of space
    and prevent me from having the entire frontpage in one
    screen.
    Nu Compact removes the pictures on the frontpage, by
    transforming stories with pictures to plain links. Also, I
    know what the current date is and the nu.nl logo takes up
    too much space, so Nu Compact removes them.


    Known bugs:
    * We should also remove the stupid column soundbites on
      the right side of the frontpage.
    * We should render the entire page black and suggest some
      other source for news.


    Changelog

    2007-04-03 - 0.2.1
    * Also remove logo and date
    * Added known bugs

    2007-04-03 - 0.2
    * Adapted to new nu.nl layout

    2005-05-29 - 0.1
    * Initial version


    Nu Compact is Open Source and licensed under the new
    BSD License, found at:
    http://www.opensource.org/licenses/bsd-license.php
*/



/*
    Wrap the whole thing in an anonymous function to avoid
    nameclashes with existing Javascript.
*/
(function() {


function rewritePicturizedStories() {

    var stories, story, link, links, newLink, header;

    var sections = [
            {
                title: 'Algemeen',
                color: 'a9d9ff',
                class: 'verloopAlgemeen',
                icon: 'img/ico_pijl_1.gif'
            },
            {
                title: 'Economie',
                color: 'ffbdbd',
                class: 'verloopBeurs',
                icon: 'images/ico_pijl_2.gif'
            },
            {
                title: 'Internet',
                color: 'cac6f7',
                class: 'verloopInternet',
                icon: 'images/ico_pijl_3.gif'
            },
            {
                title: 'Sport',
                color: 'bde7bd',
                class: 'verloopSport',
                icon: 'images/ico_pijl_4.gif'
            },
            {
                title: 'Overig',
                color: 'f5e47f',
                class: 'verloopOverig',
                icon: 'images/ico_pijl_5.gif'
            }
    ];

    var xpath_sections = sections.map
        ( function(s) { return "(@class='" + s.class + "')"; } ).join(" or ");
    xpath_sections = "//tr[" + xpath_sections + "]";

    // Find containers for picturized stories
    stories = document.evaluate(xpath_sections,
                                document,
                                null,
                                XPathResult.UNORDERED_NODE_SNAPSHOT_TYPE,
                                null);

    for (var i = 0; i < stories.snapshotLength; i++) {

        story = stories.snapshotItem(i);

        // The link containing url and title of story
        link = document.evaluate(".//td[@valign]//a[@class='link']",
                                 story,
                                 null,
                                 XPathResult.FIRST_ORDERED_NODE_TYPE,
                                 null).singleNodeValue;

        // Placeholder for plain links to stories
        links = document.evaluate("./following::td/div",
                                  story,
                                  null,
                                  XPathResult.FIRST_ORDERED_NODE_TYPE,
                                  null).singleNodeValue;

        // Create new link container div
        newLink = document.createElement('div');

        if (i < sections.length) {
            icon = sections[i].icon;
        } else {
            icon = '/img/ico_pijl_1.gif';
        }

        // Ok, this is ugly
        newLink.innerHTML =
            '<b><img src="' + icon + '" border="0" alt="" width="4" height="7"' +
            ' hspace="4" vspace="0" class="pijl1"> <a class="link" href="' +
            link.getAttribute('href') + '"> ' + link.firstChild.nodeValue +
            '</a></b><br>';

        // Add plain link for this story
        links.insertBefore(newLink, links.firstChild);

        // Empty original section for story (including the picture)
        while (story.firstChild) {
            story.removeChild(story.firstChild);
        }

        // Create a section header
        if (i < sections.length) {
            header = document.createElement('td');
            header.style.background = '#' + sections[i].color;
            header.style.width = '364px';
            header.appendChild(document.createTextNode(sections[i].title));
        }

        // Place section header
        story.appendChild(header);

    }

}


function removeUselessHeader() {

    var header;

    // Find the useless header (it contains a td with class 'noprint')
    header = document.evaluate("//tr[td[@class='noprint']]",
                               document,
                               null,
                               XPathResult.FIRST_ORDERED_NODE_TYPE,
                               null).singleNodeValue;

    // Hide it because it's useless
    header.parentNode.removeChild(header);

}


removeUselessHeader();
rewritePicturizedStories();


/*
    End of wrapper function (see top of script).
*/
})();
