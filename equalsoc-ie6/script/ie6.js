/*
  Add some event handlers to compensate for IE6 incompetence.
*/
function addHandlers() {

    var subnav, buttons;

    if (subnav = document.getElementById('subnav')) {

        for (var i = 0; i < subnav.childNodes.length; i++) {
            var li = subnav.childNodes[i];
            // IE6 doesn't know double class selectors, so we have to
            // explicitely restrict ourselves to li.hover elements.
            if (li.tagName == 'LI' && hasClassName(li, 'folder'))
                addHoverEvent(li);
        }

    }

    buttons = document.getElementsByTagName('BUTTON');

    for (var i = 0; i < buttons.length; i++)
        addHoverEvent(buttons[i]);

}


/*
  Add the 'hover' class to this element on mouse hover.
*/
function addHoverEvent(el) {
    el.onmouseover = function() { addClassName(this, 'hover');    };
    el.onmouseout  = function() { removeClassName(this, 'hover'); };
}


/*
  Do the magic.
*/
if (window.attachEvent)
    window.attachEvent("onload", addHandlers);


/*
  Test if element has given class.
*/
function hasClassName(el, name) {

    var i, list;

    list = el.className.split(" ");
    for (i = 0; i < list.length; i++)
        if (list[i] == name)
            return true;

    return false;

}


/*
  Remove given class from element.
*/
function removeClassName(el, name) {

    var i, curList, newList;

    if (el.className == null)
        return;

    newList = new Array();
    curList = el.className.split(" ");
    for (i = 0; i < curList.length; i++)
        if (curList[i] != name)
            newList.push(curList[i]);
    el.className = newList.join(" ");

}


/*
  Add given class to element.
*/
function addClassName(el, name) {
    el.className += " " + name;
}
