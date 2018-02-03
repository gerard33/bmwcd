#! /usr/bin/env python3
""" BMW ConnectedDrive API

Attributes:
    username (int): BMW ConnectedDrive username (email)
    password (string): BMW ConnectedDrive password
    vin (string): 17 chars Vehicle Identification Number (VIN) of the car, can be found in the app or on BMW ConnectedDrive online
    url(string): URL you use to login to BMW ConnectedDrive, e.g. 'www.bmw-connecteddrive.nl' or 'www.bmw-connecteddrive.de'
    update_interval (int): update intervall in minutes
"""

# **** bmwcdapi.py ****
# https://github.com/jupe76/bmwcdapi
#
# Query vehicle data from the BMW ConnectedDrive Website, i.e. for BMW i3
# Based on the excellent work by Sergej Mueller
# https://github.com/sergejmueller/battery.ebiene.de
#
# Permission to use, copy, modify, and distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
# WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
# ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
# ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
# OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

# ----======================================================================================================----
# This version is made by Gerard for use in Home Assistant and based on the above bmwcdapi.py script from jupe76
#
# Also inspiration came from https://github.com/frankjoke/ioBroker.bmw/blob/master/connectedDrive.js and
# https://www.symcon.de/forum/threads/36747-BMW-connected-drive-in-IPS?p=349074
# ----======================================================================================================----

import logging
import sys
import json
import time
import urllib.parse
import re
import argparse
import xml.etree.ElementTree as etree
from multiprocessing import RLock
from datetime import datetime
import requests
from requests.exceptions import HTTPError
#from bmwcdapi import Exceptions as BMWException
from Exceptions import BMWConnectedDriveException as BMWException

root = logging.getLogger()
root.setLevel(logging.INFO)

ch = logging.StreamHandler(sys.stdout)
ch.setLevel(logging.INFO)
formatter = logging.Formatter('%(asctime)s - %(message)s')
ch.setFormatter(formatter)
root.addHandler(ch)

#############################################################################################################################
# Enter the data below between quotes to be able to run the script from CLI
USERNAME = None         # Your BMW ConnectedDrive username
PASSWORD = None         # Your BMW ConnectedDrive password
VIN = None              # 17 chars Vehicle Identification Number (VIN) of the car, check the app of BMW ConnectedDrive Online
URL = None              # URL without 'https://' to login to BMW ConnectedDrive, e.g. 'www.bmw-connecteddrive.nl'
CAR_NAME = None         # This is the name of your car
UPDATE_INTERVAL = 10    # The interval in minutes to check the API, don't hammer it, default = 30 mins, minimum is 10 mins
#############################################################################################################################

_LOGGER = logging.getLogger(__name__)
TIMEOUT = 10

AUTH_API = 'https://customer.bmwgroup.com/gcdm/oauth/authenticate'
USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:57.0) Gecko/20100101 Firefox/57.0"

###
# https://www.bmw-connecteddrive.de/api/vehicle/navigation/v1/VIN
# https://www.bmw-connecteddrive.de/api/vehicle/image/v1/VIN?startAngle=10&stepAngle=10&width=780
# https://www.bmw-connecteddrive.de/api/vehicle/dynamic/v1/VIN?offset=-60
# https://www.bmw-connecteddrive.de/api/vehicle/efficiency/v1/VIN
# https://www.bmw-connecteddrive.de/api/me/vehicles/v2 --> CARS
# https://www.bmw-connecteddrive.de/api/me/service/mapupdate/download/v1/VIN
# https://www.bmw-connecteddrive.de/api/vehicle/specs/v1/VIN
# https://www.bmw-connecteddrive.de/api/vehicle/service/v1/VIN
# https://www.bmw-connecteddrive.de/api/vehicle/servicepartner/v1/VIN
# https://www.bmw-connecteddrive.de/api/vehicle/remoteservices/chargingprofile/v1/VIN
# https://www.bmw-connecteddrive.de/api/vehicle/remoteservices/v1/VIN/history
###

class ConnectedDrive(object):
    """ BMW ConnectedDrive """
    def __init__(self, username=USERNAME, password=PASSWORD, vin=VIN, url=URL, car_name=CAR_NAME, update_interval=UPDATE_INTERVAL):
        self._lock = RLock()
        self.printall = False
        self.bmw_username = username
        self.bmw_password = password
        self.bmw_vin = vin
        self.car_name = car_name
        self.update_interval = update_interval * 60     # From minutes to seconds
        self.is_valid_session = False
        self.last_update_time = 0
        self.is_updated = False
        self.bmw_url = 'https://{}/api/vehicle'.format(url)
        self.bmw_url_me = 'https://{}/api/me'.format(url)
        self.accesstoken = None
        self.token_expires = 0
        self.token_expires_date_time = 0
        self.utc_offset_min = 0
        self.ignore_interval = None
        self.map_car_data = {}

        self.utc_offset_min = int(round((datetime.utcnow() - datetime.now()).total_seconds()) / 60)
        _LOGGER.info("UTC offset: %s minutes", self.utc_offset_min)
      
        self.generate_credentials() # Get credentials
        if self.is_valid_session:   # Get data
            self.update()

    def update(self):
        """ Simple BMW ConnectedDrive API.
            Updates every x minutes as set in the update interval.
        """
        cur_time = time.time()
        with self._lock:
            if cur_time - self.last_update_time > self.update_interval:
                result = self.get_car_data()    # Get new data
                self.last_update_time = time.time()
                _LOGGER.info("BMW ConnectedDrive API: data collected from car")
                _LOGGER.debug("map_car_data: %s", self.map_car_data)
                self.is_updated = True
                return result

            _LOGGER.debug("BMW ConnectedDrive API: no data collected from car as interval has not yet passed")
            self.is_updated = False
            return False

    def token_valid(self):
        """Check if token is still valid, if not make new token."""
        cur_time = time.time()
        if int(cur_time) >= int(self.token_expires):
            self.generate_credentials()
            _LOGGER.info("BMW ConnectedDrive API: new credentials obtained (token expires at: %s)",
                         self.token_expires_date_time)
        else:
            _LOGGER.info("BMW ConnectedDrive API: current credentials still valid (token expires at: %s)",
                         self.token_expires_date_time)

    def generate_credentials(self):
        """If previous token has expired, create a new one."""
        headers = {
            "Content-Type": "application/x-www-form-urlencoded",
            "User-agent": USER_AGENT
        }
        values = {
            'username' : self.bmw_username,
            'password' : self.bmw_password,
            'client_id' : 'dbf0a542-ebd1-4ff0-a9a7-55172fbfce35',
            'redirect_uri' : 'https://www.bmw-connecteddrive.com/app/default/static/external-dispatch.html',
            'response_type' : 'token',
            'scope' : 'authenticate_user fupo',
            'state' : 'eyJtYXJrZXQiOiJkZSIsImxhbmd1YWdlIjoiZGUiLCJkZXN0aW5hdGlvbiI6ImxhbmRpbmdQYWdlIn0',
            'locale' : 'DE-de'
        }

        data = urllib.parse.urlencode(values)
        credentials_response = requests.post(AUTH_API, data=data, headers=headers, allow_redirects=False)
        # statuscode will be 302
        _LOGGER.info("BMW ConnectedDrive API: credentials response code: %s",
                      credentials_response.status_code)
        my_payload = credentials_response.headers['Location']
        result_m = re.match(".*access_token=([\w\d]+).*token_type=(\w+).*expires_in=(\d+).*", my_payload)
        
        # token_type = result_m.group(2)
        self.accesstoken = result_m.group(1)
        self.token_expires = int(time.time()) + int(result_m.group(3))
        self.token_expires_date_time = time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(self.token_expires))

        if self.accesstoken:
            self.is_valid_session = True
        else:
            self.is_valid_session = False

    def request_car_data(self, data_type, sub_data_type=None):
        """Get data from BMW Connected Drive."""
        headers = {
            'Content-Type': 'application/json',
            'User-agent': USER_AGENT,
            'Authorization' : 'Bearer ' + self.accesstoken
        }

        self.token_valid()  # Check if current token is still valid

        if data_type == 'dynamic':
            url = '{}/{}/v1/{}?offset={}'.format(self.bmw_url, data_type, self.bmw_vin, str(self.utc_offset_min))
        elif data_type == 'get_cars':
            url = '{}/vehicles/v2'.format(self.bmw_url_me) # https://www.bmw-connecteddrive.nl/api/me/vehicles/v2
        else:
            url = '{}/{}/v1/{}'.format(self.bmw_url, data_type, self.bmw_vin)
        
        data_response = requests.get(url,
                                     headers=headers,
                                     allow_redirects=True) ###Timeout
        
        try:
            _LOGGER.info("BMW ConnectedDrive API: connect to URL %s", url)
            data_response.raise_for_status()
        except HTTPError as error_message:  # Whoops it wasn't a 200
            _LOGGER.info("Error code: %s (%s)", error_message.response.status_code, error_message)
            raise BMWException(error_message.response.status_code)

        if data_type == 'dynamic' or data_type == 'servicepartner':
            return data_response.json()[sub_data_type]
        else:
            return data_response.json()
    
    def get_car_data(self):
        """Get car data from BMW Connected Drive."""
        
        self.map_car_data = self.request_car_data('dynamic', 'attributesMap')

        if self.printall:
            _LOGGER.info('--------------START CAR DATA--------------')
            for key in sorted(self.map_car_data):
                _LOGGER.info("%s: %s", key, self.map_car_data[key])
            #print(json.dumps(map_car_data, sort_keys=True, indent=4))
            _LOGGER.info('--------------END CAR DATA--------------')

        return self.map_car_data

    def get_cars(self):
        """Get car data from BMW Connected Drive."""
        
        map_cars = self.request_car_data('get_cars')

        if self.printall:
            _LOGGER.info('--------------START CARS--------------')
            # Contains a list with a dict in it
            for i in map_cars:
                car_number = 1
                _LOGGER.info("Car %s of %s", car_number, str(len(map_cars)))
                for key in sorted(i):
                    _LOGGER.info("%s: %s", key, i[key])
                car_number += 1
            _LOGGER.info('--------------END CARS--------------')

        return map_cars

    def get_car_data_service(self):
        """Get car data from BMW Connected Drive."""

        map_car_data_service = self.request_car_data('dynamic', 'vehicleMessages')

        if self.printall:
            _LOGGER.info('--------------START CAR DATA SERVICE--------------')
            for key in sorted(map_car_data_service):
                _LOGGER.info("%s: %s", key, map_car_data_service[key])
            _LOGGER.info('--------------END CAR DATA SERVICE--------------')

        return map_car_data_service

    def get_car_navigation(self):
        """Get navigation data from BMW Connected Drive."""

        map_car_navigation = self.request_car_data('navigation')

        if self.printall:
            _LOGGER.info('--------------START CAR NAV--------------')
            for key in sorted(map_car_navigation):
                _LOGGER.info("%s: %s" % (key, map_car_navigation[key]))
            _LOGGER.info('--------------END CAR NAV--------------')

        return map_car_navigation

    def get_car_efficiency(self):
        """Get efficiency data from BMW Connected Drive."""

        map_car_efficiency = self.request_car_data('efficiency')

        if self.printall:
            _LOGGER.info('--------------START CAR EFFICIENCY--------------')
            for key in sorted(map_car_efficiency):
                _LOGGER.info("%s: %s" % (key, map_car_efficiency[key]))
            _LOGGER.info('--------------END CAR EFFICIENCY--------------')

        return map_car_efficiency

    def get_car_service_partner(self):
        """Get servicepartner data from BMW Connected Drive."""
        
        map_car_service_partner = self.request_car_data('servicepartner', 'dealer')

        if self.printall:
            _LOGGER.info('--------------START CAR SERVICEPARTNER--------------')
            for key in sorted(map_car_service_partner):
                _LOGGER.info("%s: %s" % (key, map_car_service_partner[key]))
            _LOGGER.info('--------------END CAR SERVICEPARTNER--------------')

        return map_car_service_partner

    def execute_service(self, service):
        """Get servicepartner data from BMW Connected Drive."""

        self.token_valid()  # Check if current token is still valid

        max_retries = 9
        interval = 10 #secs

        service_codes = {
            'climate': 'RCN',
            'lock': 'RDL',
            'unlock': 'RDU',
            'light': 'RLF',
            'horn': 'RHB'
        }

        headers = {
            "Content-Type": "application/json",
            "User-agent": USER_AGENT,
            "Authorization" : "Bearer "+ self.accesstoken
        }

        _LOGGER.info("Executing service %s", service)
        command = service_codes[service]
        remote_service_status = None
        url = '{}/remoteservices/v1/{}/{}'.format(self.bmw_url, self.bmw_vin, command)
        url_check = '{}/remoteservices/v1/{}/state/execution'.format(self.bmw_url, self.bmw_vin)

        execute_response = requests.post(url,
                                         headers=headers,
                                         allow_redirects=True)

        if execute_response.status_code != 200:
            _LOGGER.error("Error during executing service %s", service)
            return False

        for i in range(max_retries):
            time.sleep(interval)
            remoteservices_response = requests.get(url_check,
                                                   headers=headers,
                                                   allow_redirects=True)
            _LOGGER.debug("Status execstate %s %s", str(remoteservices_response.status_code), remoteservices_response.text)
            root_data = etree.fromstring(remoteservices_response.text)
            remote_service_status = root_data.find('remoteServiceStatus').text
            #print(remoteServiceStatus)
            if remote_service_status == 'EXECUTED':
                _LOGGER.info("Executing service %s succeeded", service)
                break

        if remote_service_status != 'EXECUTED':
            _LOGGER.error("Error during executing service %s, timer expired", service)
            return False

        return True

def main():
    """Show information when this script is started from CLI."""
    _LOGGER.info("...running bmwcdapi.py")
    c = ConnectedDrive()

    parser = argparse.ArgumentParser()
    parser.add_argument('-p', '--printall', action='store_true',
                        help='print all values that were received')
    parser.add_argument('-e', '--execservice', dest='service',
                        choices=['climate', 'lock', 'unlock', 'light', 'horn'],
                        action='store', help='execute service like instant climate control')
    args = vars(parser.parse_args())

    if args["printall"]:
        c.printall = True

    # dont query data and execute the service at the same time, takes too long
    if args["service"]:
        # execute service
        c.execute_service(args["service"])
    else:
        c.get_car_data()
        c.get_cars()
        #c.get_car_navigation()
        #c.get_car_efficiency()
        #c.get_car_service_partner()

    return

if __name__ == '__main__':
    main()
