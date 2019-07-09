# this the interface to create your own data source
# this class pings etherscan to get the latest code and balance information

import requests
import logging

log = logging.getLogger(__name__)

class EthereumData:
        def __init__(self):
            self.apiDomain = "https://api.etherscan.io/api"
            self.apikey = "6MZ7MBW1DAQM2PAETE3ZPAK9377Y7ZX2CJ"

        def getBalance(self, address):  # address should be string
            try:
                apiEndPoint = "%s?module=account&action=balance&address=%s&tag=latest&apikey=%s" % (self.apiDomain, address, self.apikey)
                r = requests.get(apiEndPoint)
                result = r.json()
                status = result['message']
                if status == "OK":
                    result = result['result']
            except Exception as e:
                log.exception("Error at: contract address: %s" % address)
                raise e
            return result

        def getCode(self, address):
            try:
                apiEndPoint = "%s?module=proxy&action=eth_getCode&address=%s&tag=latest&apikey=%s" % (self.apiDomain, address, self.apikey)
                r = requests.get(apiEndPoint)
                result = r.json()["result"]
            except Exception as e:
                log.exception("Error at: contract address: %s" % address)
                raise e
            return result
