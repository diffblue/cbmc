"""CBMC viewer configuration."""

import logging
import json

class Config:
    """Manage CBMC viewer configuration settings."""

    def __init__(self, config=None):
        self.file = config
        self.missing_functions = None

        if config is None:
            return

        try:
            with open(config) as data:
                settings = json.load(data)
                self.missing_functions = (
                    # understand it is dangerous to use setting.get(xxxx, [])
                    settings.get('expected-missing-functions') or []
                )
        except FileNotFoundError as error:
            logging.info("Can't open %s: %s", config, error.strerror)

    def expected_missing_functions(self):
        """Return list of expected missing functions."""

        return self.missing_functions
