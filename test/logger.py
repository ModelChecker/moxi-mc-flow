import logging
import re
import sys

class Color:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    PASS = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

class Formatter(logging.Formatter):
    format_str = '%(levelname)s'

    FORMATS = {
        logging.DEBUG: format_str + ': %(message)s',
        logging.INFO: '%(message)s',
        logging.WARNING: format_str + ': %(message)s',
        logging.ERROR: format_str + ': %(message)s',
        logging.CRITICAL: format_str + ': %(message)s',
    }

    def format(self, record) -> str:
        record.msg = re.sub(r"\033\[\d\d?m", "", record.msg) # removes color from msg
        log_fmt = self.FORMATS.get(record.levelno)
        formatter = logging.Formatter(log_fmt)
        return formatter.format(record)

class ColorFormatter(logging.Formatter):
    format_str = '%(levelname)s'

    FORMATS = {
        logging.DEBUG: Color.OKBLUE + format_str + Color.ENDC + ': %(message)s',
        logging.INFO: '%(message)s',
        logging.WARNING: Color.WARNING + format_str + Color.ENDC + ': %(message)s',
        logging.ERROR: Color.FAIL + format_str + Color.ENDC + ': %(message)s',
        logging.CRITICAL: Color.UNDERLINE + Color.FAIL + format_str + Color.ENDC + ': %(message)s'
    }

    def format(self, record):
        log_fmt = self.FORMATS.get(record.levelno)
        formatter = logging.Formatter(log_fmt)
        return formatter.format(record)

toplevel_logger = logging.getLogger(__name__)
toplevel_logger.setLevel(logging.DEBUG)

stream_handler = logging.StreamHandler(sys.stdout)
stream_handler.setLevel(logging.DEBUG)
stream_handler.setFormatter(ColorFormatter())
toplevel_logger.addHandler(stream_handler)