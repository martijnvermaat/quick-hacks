#!/usr/bin/env python

"""
File upload example with web.py.

Just run this file directly to use the built-in webserver, or add the
following to your Apache configuration:

    Alias /upload/static /var/www/webpy-upload/static
    WSGIScriptAlias /upload /var/www/webpy-upload/upload.py
    AddType text/html .py

Then go to the /upload subpath, e.g. http://0.0.0.0:8080/upload
"""


import os
import tempfile
import cgi
import web
from web.contrib.template import render_jinja
from web.http import urlencode


# Maximum size for uploaded files in megabytes
MAX_UPLOAD_SIZE = 50
cgi.maxlen = MAX_UPLOAD_SIZE * 1024 * 1024

# Set to False to disable fancy web.py stack trace views
web.config.debug = True


# URL routing
urls = ('/upload', 'Upload',
        '/thanks', 'Thanks')

# Render templates with Jinja2
render = render_jinja(os.path.join(os.path.dirname(__file__), 'templates'),
                      encoding='utf-8')

# Our web.py application
app = web.application(urls, globals())


class Upload:
    """
    Handle uploading and storing of files.
    """
    def GET(self):
        """
        Show file upload form.
        """
        return render.upload()

    def POST(self):
        """
        Store uploaded file.
        """
        try:
            i = web.input(file={}, name='No Name')
        except ValueError:
            return render.error(message='Sorry, only files up to %d'
                                ' megabytes are accepted.' % MAX_UPLOAD_SIZE)

        # Check if we have everything we need
        if not 'file' in i or i.file == None or not i.file.file or not i.name:
            return render.error(message='No name and/or file provided.')

        # Store the file under a temporary path
        fd, filename = tempfile.mkstemp(suffix='.vcf', prefix='upload-')
        handle = os.fdopen(fd, 'w')
        handle.write(i.file.file.read())
        handle.close()
        web.seeother('/thanks?%s' % urlencode({'file': filename,
                                               'name': i.name}))


class Thanks:
    """
    Show a thank you page after uploading.
    """
    def GET(self):
        """
        Show thanks page.
        """
        i = web.input(name='No name', file='no file')
        return render.thanks(name=i.name, file=i.file)


# WSGI handler
application = app.wsgifunc()


if __name__ == '__main__':
    # Built-in webserver
    app.run()
