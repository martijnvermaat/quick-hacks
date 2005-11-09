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
pygtk.require('2.0')
import gtk
import gtk.glade

#import pysvn


def actionCheckout(dir):
    d = CheckoutDialog()
    d.run(dir)
    return


class CheckoutDialog:


    def __init__(self):

        self.xml = gtk.glade.XML(GLADEFILE)
        self.window = self.xml.get_widget("windowCheckout")

        self.xml.signal_autoconnect({
            "on_cancel": self.__on_cancel,
            })

        self.window.connect("destroy", self.__on_destroy)

        self.window.show()

        return


    def run(self, dir):
        self.xml.get_widget("directoryEntry").set_text(dir)
        gtk.main()
        return


    def __on_cancel(self, w):
        self.window.destroy()
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
