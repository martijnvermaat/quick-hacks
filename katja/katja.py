#!/usr/bin/env python


"""
Katja, a Gtk Subversion client.
"""


VERSION = "0.1"
DATE = "2005/11/09"

GLADEFILE = "katja.glade"


import os
from optparse import OptionParser

import pygtk
pygtk.require("2.0")
import gtk
import gtk.glade

import pysvn


def actionCheckout(dir):
    d = CheckoutDialog()
    d.run(dir)
    return


class CheckoutDialog:


    # TODO: all 'real' code should be moved out of this class, probably to
    # the actionCheckout class


    widget_names = ["windowCheckout",
                    "repositoryEntry",
                    "directoryEntry",
                    "locationChooser",
                    "revisionChoiceHead",
                    "revisionChoiceSpin",
                    "revisionSpin"]


    def __init__(self):

        self.xml = gtk.glade.XML(GLADEFILE, "windowCheckout")

        self.widgets = {}
        for w in self.widget_names:
            self.widgets[w] = self.xml.get_widget(w)

        self.xml.signal_autoconnect(
            {"on_cancel": self.__on_cancel,
             "on_checkout": self.__on_checkout,
             "on_revision_toggled": self.__on_revision_toggled})

        self.widgets["windowCheckout"].connect("destroy", self.__on_destroy)

        return


    def run(self, dir):

        self.widgets["locationChooser"].set_current_folder(dir)

        self.widgets["revisionChoiceHead"].set_active(1)
        self.widgets["revisionSpin"].set_sensitive(0)

        self.widgets["windowCheckout"].show()
        gtk.main()

        return


    def __on_revision_toggled(self, w):
        if self.widgets["revisionChoiceSpin"].get_active():
            self.widgets["revisionSpin"].set_sensitive(1)
        else:
            self.widgets["revisionSpin"].set_sensitive(0)
        return


    def __on_cancel(self, w):
        self.widgets["windowCheckout"].destroy()
        return


    def __on_checkout(self, w):

        client = pysvn.Client()
        client.exception_style = 0  # Would prefer 1, but doesn't seem to work

        url = self.widgets["repositoryEntry"].get_text()
        if url[-1] == '/':
            url = url[:-1]

        path = os.path.join(
            self.widgets["locationChooser"].get_current_folder(),
            self.widgets["directoryEntry"].get_text())

        try:
            client.checkout(url, path)
        except pysvn.ClientError, e:
            # e.arg[0]  entire message
            # e.arg[1]  list of tupels (code, message)
            error_dialog("Checkout failed",
                         str(e),
                         self.widgets["windowCheckout"])
            return

        print int(self.widgets["revisionSpin"].get_value())
        self.__on_cancel(w)
        return


    def __on_destroy(self, w):
        gtk.main_quit()
        return



def error_dialog(title, message, parent):

    #def hoi(w):
    #    print "hoi"

    #d = gtk.Dialog(title, parent=parent, buttons=("_Close", 1))

    #label = gtk.Label(message)
    #d.vbox.pack_start(label, True, True, 0)
    #label.show()

    #d.run()

    error = gtk.MessageDialog(parent=parent,
                              buttons=gtk.BUTTONS_CLOSE,
                              type=gtk.MESSAGE_ERROR,
                              flags=gtk.DIALOG_MODAL)

    error.set_markup("<b>" + title + "</b>\n\n" + message)

    error.run()
    error.destroy()

    return


def main():

    """
    Parse command line options.
    """

    parser = OptionParser(usage = "usage: %prog <command> [options] [args]",
                          version = "Katja %s (%s)" % (VERSION, DATE),
                          description = "Katja is a graphical Subversion "
                          "client.")

    (options, args) = parser.parse_args()

    if len(args) < 1:
        parser.error("no command provided")

    if args[0] == "checkout":
        actionCheckout(os.getcwd())
    else:
        parser.error("command '%s' not recognised" % args[0])

    return


if __name__ == "__main__":
    main()
