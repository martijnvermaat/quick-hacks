#!/usr/bin/env python

# Annotate variants using SeattleSeq Annotation.
#
# Given a VCF file with variants, submit the file to the SeattleSeq Annotation
# web interface. The annotation result is retrieved as gzipped tab-separated
# file.
#
# Usage:
#   ./seattle_seq_annotation.py <input.vcf>
#
# The result is written to disk as <input.vcf.annotation.gz>.
#
# Requires the poster Python library: http://atlee.ca/software/poster/
#
# 2011-02-09, Martijn Vermaat <m.vermaat.hg@lumc.nl>


# E-mail address to use in submit (job result will be mailed there)
EMAIL = 'm.vermaat.hg@lumc.nl'

# Seconds to wait between polling for job result
WAIT_STEP = 5

# Maximum seconds to wait for job result
WAIT_MAX = 180

# Print debugging information
DEBUG = True

# Columns to include
COLUMNS = ['sampleAlleles',
#           'dbSNPGenotype',
           'allelesDBSNP',
           'scorePhastCons',
           'consScoreGERP',
           'chimpAllele',
           'CNV',
           'geneList',
           'HapMapFreq',
           'hasGenotypes',
           'dbSNPValidation',
           'repeats',
           'proteinSequence',
           'polyPhen',
#           'distanceToSplice',
#           'microRNAs',
           'clinicalAssociation']


import sys
import re
import time
from poster.encode import multipart_encode
from poster.streaminghttp import register_openers
import urllib
import urllib2


# Some ugly urls
BASE_URL = 'http://gvs.gs.washington.edu/SeattleSeqAnnotation131/'
POST_URL = BASE_URL + 'BatchQueryServlet'
MONITOR_URL_SCHEME = BASE_URL + 'BatchProgressServlet?progressFile=' \
                     + 'AnnotationProgress.{job}.txt&submittedFile={file}&' \
                     + 'cancelFile=AnnotationCancel.{job}.txt&isVCFIn=true&' \
                     + 'isVCFOut=false'
TABLE_URL_SCHEME = BASE_URL + 'AnnotationReadBackServlet?clickType=direct&' \
                   + 'progressFile=AnnotationProgress.{job}.txt'
RESULT_URL_SCHEME = 'http://gvs-p.gs.washington.edu/SeattleSeqAnnotation131' \
                    + '/BatchFileDownloadServlet?file={file}.gz&download=true'


def seattle_seq_annotation(vcf_file):
    """
    Submit a VCF file to the SeattleSeq Annotation web interface. The
    annotation result is retrieved as gzipped tab-separated and written to
    disk.
    """
    job_id, submitted_file = submit_vcf_file(vcf_file)
    wait_for_result(job_id, submitted_file)
    result_file = get_result_file(job_id, submitted_file)
    write_result_file(result_file, vcf_file + '.annotation.gz')


def submit_vcf_file(vcf_file):
    """
    Submit a VCF file to the SeattleSeq Annotation server and return as a
    tuple the job id and the name of the submitted file.
    """
    try:
        vcf = open(vcf_file, 'r')
    except IOError as (_, message):
        fatal_error(message)

    parameters = [('genotypeSource',   'FileInput'),
                  ('EMail',            EMAIL),
                  ('GenotypeFile',     vcf),
                  ('fileFormat',       'VCF'),
                  ('outputFileFormat', 'original'),
                  ('geneData',         'NCBI'),
                  ('HapMapFreqType',   'HapMapFreqMinor'),
                  ('gFetch',           'Display Genotypes')]
    for column in COLUMNS:
        parameters.append( ('columns', column) )

    submit = post_multipart(POST_URL, parameters)
    submit_url = submit.geturl()

    debug('Submit url: %s' % submit_url)

    # Get job id from url
    match = re.search(r'progressFile=AnnotationProgress\.(\d+)\.txt',
                      submit_url)
    if not match:
        fatal_error('Could not find job id in submit url.')
    job_id = match.group(1)

    # Get submitted file from url
    match = re.search(r'submittedFile=([^=&]+)',
                      submit_url)
    if not match:
        fatal_error('Could not find submitted file in submit url.')
    submitted_file = match.group(1)

    debug('Job id: %s' % job_id)
    debug('Submitted file: %s' % submitted_file)

    return job_id, submitted_file


def wait_for_result(job_id, submitted_file):
    """
    Monitor the job for progress. Return when the job is completed.
    """
    monitor_url = MONITOR_URL_SCHEME.format(job=job_id, file=submitted_file)

    debug('Monitor url: %s' % monitor_url)

    waiting = 0
    while True:
        if waiting > WAIT_MAX:
            fatal_error('Job took too long (monitor url: %s)' % monitor_url)

        time.sleep(WAIT_STEP)
        waiting += WAIT_STEP

        monitor = get(monitor_url).read()

        # Check if we have a monitor page that looks sane
        if monitor.find('in your file have been processed') == -1:
            fatal_error('Could not monitor job (monitor_url: %s)'
                        % monitor_url)

        # Find a progress > 0% (the message is different in that case)
        progress = re.search(r'(\d+) out of (\d+) variations', monitor)
        if not progress:
            debug('Waiting: 0%')
            continue

        processed, total = progress.group(1), progress.group(2)

        debug('Waiting: %s / %s' % (processed, total))

        # See if we are done
        if processed == total:
            break


def get_result_file(job_id, submitted_file):
    """
    For a (completed) job, get the result file name.

    It is unfortunate that we can only get the location of the plain text
    result file from the HTML table (okay, also from the e-mail).
    So we read in the HTML table (big) and construct the url to the plain
    text result.
    """
    table_url = TABLE_URL_SCHEME.format(job=job_id, file=submitted_file)

    debug('Table url: %s' % table_url)

    table = get(table_url)

    result_file = None
    while True:
        line = table.readline()
        if not line:
            break
        result_text = re.search(r'<big>/jboss/gvsBatchOutput/(SeattleSeqAnnotation131\.[\w\d_\.-]+\.txt)</big>',
                                line)
        if result_text:
            result_file = result_text.group(1)
            break

    table.close()
    if not result_file:
        fatal_error('Could not find result file name in table page.')

    return result_file


def write_result_file(result_file, output_file):
    """
    Get gzipped result from server and write it to a file.

    @todo: Maybe we should read/write buffered.
    """
    result_url = RESULT_URL_SCHEME.format(file=result_file)

    debug('Result url: %s' % result_url)

    # This is gzipped
    result = get(result_url).read()

    try:
        output = open(output_file, 'wb')
    except IOError as (_, message):
        fatal_error(message)

    output.write(result)
    output.close()


def get(url):
    """
    Do a HTTP GET request and return file-like response object.
    """
    request = urllib2.Request(url)
    #request.add_header('Cookie', 'JSESSIONID=xxx')
    response = urllib2.urlopen(request)
    return response


def post_multipart(url, parameters={}):
    """
    Do a HTTP POST request encoded as multipart/form-data and return file-like
    response object.
    """
    register_openers()
    datagen, headers = multipart_encode(parameters)
    request = urllib2.Request(POST_URL, datagen, headers)
    #request.add_header('Cookie', 'JSESSIONID=xxx')
    response = urllib2.urlopen(request)
    return response


def debug(message):
    if DEBUG: print message


def fatal_error(message):
    print 'Error: %s' % message
    sys.exit(1)


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print """Annotate variants using SeattleSeq Annotation.

Given a VCF file with variants, submit the file to the SeattleSeq Annotation
web interface. The annotation result is retrieved as gzipped tab-separated
file.

Usage:
  ./seattle_seq_annotation.py <input.vcf>

The result is written to disk as <input.vcf.annotation.gz>."""
        sys.exit(1)
    seattle_seq_annotation(sys.argv[1])
