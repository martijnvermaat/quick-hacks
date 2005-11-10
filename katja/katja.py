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

#import pysvn


def actionCheckout(dir):
    d = CheckoutDialog()
    d.run(dir)
    return


class CheckoutDialog:


    widget_names = ["windowCheckout",
                    "revisionChoiceHead",
                    "revisionChoiceSpin",
                    "revisionSpin",
                    "locationChooser"]


    def __init__(self):

        self.xml = gtk.glade.XML(GLADEFILE)

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
        print int(self.widgets["revisionSpin"].get_value())
        self.__on_cancel(w)
        return


    def __on_destroy(self, w):
        gtk.main_quit()
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

    if args[0] == "status":
        actionCheckout(os.getcwd())

    return


if __name__ == "__main__":
    main()
