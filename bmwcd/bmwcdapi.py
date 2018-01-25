#! /usr/bin/env python3
#
# **** bmwcdapi.py ****
# https://github.com/jupe76/bmwcdapi
#
# Query vehicle data from the BMW ConnectedDrive Website, i.e. for BMW i3
# Based on the excellent work by Sergej Mueller
# https://github.com/sergejmueller/battery.ebiene.de
#
# ----=================================================----
# Above version changed by Gerard for use in Home Assistant
# ----=================================================----
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

import logging
import json
import requests
import time
from multiprocessing import RLock
import urllib.parse
import re
import argparse
import xml.etree.ElementTree as etree

###TIMEOUT toevoegen, zie https://github.com/RiRomain/python-mercedes-api/blob/master/mercedesapi/__init__.py
###TRY, EXCEPT toevoegen ook van deze url

### TO DO
### Meerdere auto's ondersteunen --> hoeft niet want ondersteund BMW ConnectedDrive niet via API

### OPTIES
### API URLs = "efficiency, dynamic, navigation, remote_execution, remote_chargingprofile, remote_history, servicepartner, service, specs";
### this._delete = ""; // "modelType, series, basicType, brand, licensePlate, hasNavi, bodyType, dcOnly, hasSunRoof, hasRex, steering, driveTrain, doorCount, vehicleTracking, isoCountryCode, auxPowerRegular, auxPowerEcoPro, auxPowerEcoProPlus, ccmMessages",
### this._flatten = "attributesMap, vehicleMessages, cbsMessages, twoTimeTimer, characteristicList, lifeTimeList, lastTripList, remoteServiceEvent";
### this._arrays = "lastTripList|name|lastTrip|unit, specs|key|value, service|name|services, cdpFeatures|name|status, cbsMessages|text|date, lifeTimeList|name|value, characteristicList|characteristic|quantity, remote_history|eventId";

### FOUTMELDINGEN GEZIEN
### 200 == goed
### 302 == onbekend
### 401 == Authotization error with {host}! Please check your credentials!
### 503 == Service unavailable. Please try later from {host}
### 404 == Not allowed?

# ----=================================================----
# Enter the data below to be able to login
# Your BMW ConnectedDrive username
USERNAME = None             # "email@gmail.com"

# Your BMW ConnectedDrive password
PASSWORD = None             # "your_password"

# 17!! chars Vehicle Identification Number (VIN) of the car, can be found in the app or on BMW ConnectedDrive online
VIN = None                  # "vin_code"

# This is the URL you use to login to BMW ConnectedDrive, e.g. www.bmw-connecteddrive.nl or www.bmw-connecteddrive.de
URL = None                  # "www.bmw-connecteddrive.nl"

# This is the name of your car
CAR_NAME = None             # "BMW X1"

# The interval in minutes to check the BMW ConnectedDrive API, don't hammer it, default = 30 mins, minimum is 10 mins
UPDATE_INTERVAL = None      # 30
# ----=================================================----

TIMEOUT = 10 ### TO DO

_LOGGER = logging.getLogger(__name__)

# API Gateway
AUTH_API = 'https://customer.bmwgroup.com/gcdm/oauth/authenticate'
###COUNTRY_CODE = 'nl'
#VEHICLE_API = 'https://{}/api/vehicle'.format(URL)
USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:57.0) Gecko/20100101 Firefox/57.0"

class ConnectedDrive(object):
    """ BMW ConnectedDrive """

    def __init__(self, username=USERNAME, password=PASSWORD, vin=VIN, url=URL, car_name=CAR_NAME, update_interval=UPDATE_INTERVAL):
        
        self._lock = RLock()
        self.printall = False
        self.bmw_username = username
        self.bmw_password = password
        self.bmw_vin = vin
        self.car_name = car_name
        self.update_interval = update_interval * 60 # Change to seconds
        self.last_update_time = 0
        self.bmw_url = 'https://{}/api/vehicle'.format(url)
        self.accesstoken = None             #"AccessToken [%s]"
        self.token_expires = 0              #"TokenExpires [%s]"    ### Wordt blijkbaar opgeslagen, nakijken of ik dat ook ergens moet doen
        self.token_expires_date_time = 0

        ###!!! NOG NAKIJKEN HOE TOKEN OPGESLAGEN WORDT https://github.com/frankjoke/ioBroker.bmw/blob/master/connectedDrive.js

        if int(time.time()) >= int(self.token_expires):
            self.generate_credentials()
            ### hier self.token_valid()

    def update(self):
        """ Simple BMW ConnectedDrive API.
            Updates every x minutes as set in the update interval.
        """
        
        cur_time = time.time()

        # with self._lock:
        #     if cur_time - self.last_update_time > self.update_interval:
        #         # Get new data
        #         result = self.get_car_data()
        #         # Update the new time
        #         self.last_update_time = time.time()
        #         _LOGGER.info("%s: data retrieved from car", self.car_name) ### nog aanpassen naar debug of info
        #         return result
            
        #     _LOGGER.debug("%s: no data retrieved from car", self.car_name)
        #     return False
        if cur_time - self.last_update_time > self.update_interval:
            # Update the new time
            self.last_update_time = time.time()
            _LOGGER.info("%s: going to collect data from car", self.car_name) ### nog aanpassen naar debug of info
            return True
            
        _LOGGER.info("%s: not going to collect data from car", self.car_name)
        return False


    def token_valid(self):
        """Check if token is still valid, if not make new token."""
        cur_time = time.time()
        if int(cur_time) >= int(self.token_expires):     ### nog aanpassen self.token_expires == 0 kan weg, want 2e deel is altijd waar is waarde == 0
            self.generate_credentials()
            _LOGGER.info("%s: new credentials from BMW Connected Drive API (token: %s expires at: %s UTC)",
                          self.car_name, self.accesstoken, self.token_expires_date_time) ### nog aanpassen naar debug of info
        else:
            _LOGGER.info("%s: current credentials from BMW Connected Drive API still valid (token: %s expires at: %s UTC)",
                          self.car_name, self.accesstoken, self.token_expires_date_time) ### nog aanpassen naar debug of info

    def generate_credentials(self):
        """
        If previous token has expired, create a new one.
        """
        headers = {
            "Content-Type": "application/x-www-form-urlencoded",
            "User-agent": USER_AGENT
        }

        values = {'username' : self.bmw_username,
            'password' : self.bmw_password,
            'client_id' : 'dbf0a542-ebd1-4ff0-a9a7-55172fbfce35',
            'redirect_uri' : 'https://www.bmw-connecteddrive.com/app/default/static/external-dispatch.html',
            'response_type' : 'token',
            'scope' : 'authenticate_user fupo',
            'state' : 'eyJtYXJrZXQiOiJkZSIsImxhbmd1YWdlIjoiZGUiLCJkZXN0aW5hdGlvbiI6ImxhbmRpbmdQYWdlIn0',
            'locale' : 'DE-de' ### NOG AANPASSEN?
        }

        data = urllib.parse.urlencode(values)
        credentials_response = requests.post(AUTH_API, data=data, headers=headers, allow_redirects=False)
        #statuscode will be 302
        #print(credentials_response.status_code)

        myPayLoad = credentials_response.headers['Location']
        m = re.match(".*access_token=([\w\d]+).*token_type=(\w+).*expires_in=(\d+).*", myPayLoad)
        
        tokenType = m.group(2)

        ### WAARDES OPSLAAN?
        self.accesstoken = m.group(1)
        ###self.ohPutValue('Bmw_accessToken',self.accesstoken)

        self.token_expires = int(time.time()) + int(m.group(3))
        #print("token expires in: " + str(self.token_expires))
        ###self.ohPutValue('Bmw_tokenExpires',self.token_expires)

        self.token_expires_date_time = time.strftime('%Y-%m-%d %H:%M:%S', time.gmtime(self.token_expires))

    # def ohPutValue(self, item, value):
    #     rc =requests.put('http://' + OPENHABIP + '/rest/items/'+ item +'/state', str(value))
    #     if(rc.status_code != 202):
    #         print("Warning: couldn't save item " + item + " to openHAB")

    # def ohGetValue(self, item):
    #     return requests.get('http://' + OPENHABIP + '/rest/items/'+ item)

    def get_car_data(self, ignore_interval=True):
        """Get data from BMW Connected Drive."""
        
        self.token_valid()  # Check if current token is still valid
        #ignore_interval = check_interval

        # Check for time interval to see if data can be retrieved again
        ### NOG VERDER TOELICHTEN
        if not ignore_interval:
            if not self.update():
                return False

        ### LOCK NOG TOEPASSEN?
        ### with self._lock:
        headers = {"Content-Type": "application/json", "User-agent": USER_AGENT, "Authorization" : "Bearer "+ self.accesstoken}

        execStatusCode = 0 #ok
        ### Try: NOG TOEVOEGEN
        data_response = requests.get(self.bmw_url+'/dynamic/v1/'+self.bmw_vin+'?offset=-60', headers=headers, allow_redirects=True)
        if data_response.status_code == 200:
            ###if map is not None and not map.get('error'):
            ###NOG CONTROLE OP VOLLEDIGHEID TOEVOEGEN
            
            ###map_car_data = {}, zodat dict.get() ook zeker goed werkt
            ### en nog als self toevoegen?
            map_car_data = data_response.json()['attributesMap']  #attributesMap, vehicleMessages, niet werkend: cbsMessages, twoTimeTimer, characteristicList, lifeTimeList, lastTripList

            #optional print all values
            if self.printall:
                print('--------------START CAR DATA--------------')
                for key in sorted(map_car_data):
                    print("%s: %s" % (key, map_car_data[key]))
                #print(json.dumps(map_car_data, sort_keys=True, indent=4))
                print('--------------END CAR DATA--------------')

            #print(type(map_car_data)) #is het een dict?
                
        else :
            print('Error with get_car_data')
            print(data_response.status_code)    ###503 --> Uw autogegevens konden niet worden geladen
            print(data_response.text)

            _LOGGER.error("Unable to communicate with BMW ConnectedDrive API. Error code: %s Reason: %s", str(data_response.status_code), data_response.text) ### nog aanpassen naar debug of info

            execStatusCode = 70 #errno ECOMM, Communication error on send
            return False ###

        return map_car_data

    def get_car_navigation(self):
        """Get navigation data from BMW Connected Drive."""
        
        self.token_valid()  # Check if current token is still valid
        
        headers = {"Content-Type": "application/json", "User-agent": USER_AGENT, "Authorization" : "Bearer "+ self.accesstoken}

        execStatusCode1 = 0 #ok

        navigation_response = requests.get(self.bmw_url+'/navigation/v1/'+self.bmw_vin, headers=headers, allow_redirects=True)
        if navigation_response.status_code == 200:
            map_car_navigation = navigation_response.json()

            #optional print all values
            if self.printall:
                print('--------------START CAR NAV--------------')
                for key in sorted(map_car_navigation):
                    print("%s: %s" % (key, map_car_navigation[key]))
                #print(json.dumps(map_car_navigation, sort_keys=True, indent=4))
                print('--------------END CAR NAV--------------')

            ###if('socMax' in map):
                #self.ohPutValue("Bmw_socMax",map['socMax'])
                #print("Bmw_socMax",map['socMax'])
        else:
            print('Error with get_car_navigation')
            print(navigation_response.status_code)
            print(navigation_response.text)
            execStatusCode1 = 70 #errno ECOMM, Communication error on send
            return False ###

        return map_car_navigation

    def get_car_efficiency(self):
        """Get efficiency data from BMW Connected Drive."""
        
        self.token_valid()  # Check if current token is still valid
        
        headers = {"Content-Type": "application/json", "User-agent": USER_AGENT, "Authorization" : "Bearer "+ self.accesstoken}

        execStatusCode2 = 0 #ok

        efficiency_response = requests.get(self.bmw_url+'/efficiency/v1/'+self.bmw_vin, headers=headers, allow_redirects=True)
        if efficiency_response.status_code == 200:
            map_car_efficiency = efficiency_response.json()
            
            if self.printall:
                print('--------------START CAR EFFICIENCY--------------')
                for key in sorted(map_car_efficiency):
                    print("%s: %s" % (key, map_car_efficiency[key]))
                #print(json.dumps(map_car_efficiency, sort_keys=True, indent=4))
                print('--------------END CAR EFFICIENCY--------------')

            ### lastTripList
            # myList=efficiency_response.json() ["lastTripList"]
            # for listItem in myList:
            #     if (listItem["name"] == "LASTTRIP_DELTA_KM"):
            #         pass
            #     elif (listItem["name"] == "ACTUAL_DISTANCE_WITHOUT_CHARGING"):
            #         pass
            #     elif (listItem["name"] == "AVERAGE_ELECTRIC_CONSUMPTION"):
            #         #self.ohPutValue("Bmw_lastTripAvgConsum", listItem["lastTrip"])
            #         print("Bmw_lastTripAvgConsum", listItem["lastTrip"])
            #     elif (listItem["name"] == "AVERAGE_RECUPERATED_ENERGY_PER_100_KM"):
            #         #self.ohPutValue("Bmw_lastTripAvgRecup", listItem["lastTrip"])
            #         print("Bmw_lastTripAvgRecup", listItem["lastTrip"])
            #     elif (listItem["name"] == "CUMULATED_ELECTRIC_DRIVEN_DISTANCE"):
            #         pass
        else:
            print('Error with get_car_efficiency')
            print(efficiency_response.status_code)
            print(efficiency_response.text)
            execStatusCode2 = 70 #errno ECOMM, Communication error on send
            return False ###

        return efficiency_response

    def get_car_service_partner(self):
        """Get servicepartner data from BMW Connected Drive."""
        
        self.token_valid()  # Check if current token is still valid
        
        headers = {"Content-Type": "application/json", "User-agent": USER_AGENT, "Authorization" : "Bearer "+ self.accesstoken}

        execStatusCode3 = 0 #ok

        service_partner_response = requests.get(self.bmw_url+'/servicepartner/v1/'+self.bmw_vin, headers=headers, allow_redirects=True)
        if service_partner_response.status_code == 200:
            map_car_service_partner = service_partner_response.json()
            my_dealer = service_partner_response.json()["dealer"]

            if self.printall:
                print('--------------START CAR SERVICEPARTNER--------------')
                #for key in sorted(map_car_service_partner):
                #    print("%s: %s" % (key, map_car_service_partner[key]))
                for key in sorted(my_dealer):
                    print("%s: %s" % (key, my_dealer[key]))
                #print(json.dumps(map_car_service_partner, sort_keys=True, indent=4))
                print('--------------END CAR SERVICEPARTNER--------------')

        else:
            print('Error with get_car_service_partner')
            print(service_partner_response.status_code)
            print(service_partner_response.text)
            execStatusCode3 = 70 #errno ECOMM, Communication error on send
            return False ###

        return service_partner_response

    def execute_service(self, service):
        # lock doors:   RDL
        # unlock doors: RDU
        # light signal: RLF
        # sound horn:   RHB
        # climate:      RCN

        #https://www.bmw-connecteddrive.de/api/vehicle/remoteservices/v1/WBYxxxxxxxx123456/history

        self.token_valid()  # Check if current token is still valid

        MAX_RETRIES = 9
        INTERVAL = 10 #secs

        print("Executing service " + service)

        serviceCodes = {
            'climate': 'RCN',
            'lock': 'RDL',
            'unlock': 'RDU',
            'light': 'RLF',
            'horn': 'RHB'}

        command = serviceCodes[service]
        headers = {
            "Content-Type": "application/json",
            "User-agent": USER_AGENT,
            "Authorization" : "Bearer "+ self.accesstoken
            }

        #initalize vars
        execStatusCode = 0
        remoteServiceStatus = ""

        execute_response = requests.post(self.bmw_url+'/remoteservices/v1/'+self.bmw_vin+'/'+command, headers=headers, allow_redirects=True)
        if execute_response.status_code != 200:
            execStatusCode = 70 #errno ECOMM, Communication error on send

        #<remoteServiceStatus>DELIVERED_TO_VEHICLE</remoteServiceStatus>
        #<remoteServiceStatus>EXECUTED</remoteServiceStatus>
        #wait max. ((MAX_RETRIES +1) * INTERVAL) = 90 secs for execution
        if execStatusCode == 0:
            for i in range(MAX_RETRIES):
                time.sleep(INTERVAL)
                remoteservices_response = requests.get(self.bmw_url+'/remoteservices/v1/'+self.bmw_vin+'/state/execution', headers=headers, allow_redirects=True)
                #print("status execstate " + str(remoteservices_response.status_code) + " " + remoteservices_response.text)
                root = etree.fromstring(remoteservices_response.text)
                remoteServiceStatus = root.find('remoteServiceStatus').text
                #print(remoteServiceStatus)
                if remoteServiceStatus == 'EXECUTED':
                    execStatusCode = 0 #OK
                    break

        if remoteServiceStatus != 'EXECUTED':
            execStatusCode = 62 #errno ETIME, Timer expired

        return execStatusCode

def main():
    print("...running bmwcdapi.py")
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
        execStatusCode = c.execute_service(args["service"])
    else:
        # else, query data
        execStatusCode = c.get_car_data()
        execStatusCode1 = c.get_car_navigation()
        execStatusCode2 = c.get_car_efficiency()
        execStatusCode3 = c.get_car_service_partner()

    #print("execStatusCode=" + str(execStatusCode))
    #print("execStatusCode1=" + str(execStatusCode1))
    #print("execStatusCode2=" + str(execStatusCode2))
    #print("execStatusCode3=" + str(execStatusCode3))
    return execStatusCode

if __name__ == '__main__':
    main()
