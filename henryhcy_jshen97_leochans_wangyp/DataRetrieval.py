import dml
import datetime
import json
import prov.model
import pandas as pd
import pprint
import uuid
from urllib.request import urlopen
import time

class DataRetrieval(dml.Algorithm):

    contributor = "henryhcy_jshen97_leochans_wangyp"
    reads = []
    writes = ['henryhcy_jshen97_leochans_wangyp.cvs', 'henryhcy_jshen97_leochans_wangyp.walgreen',
              'henryhcy_jshen97_leochans_wangyp.7eleven', 'henryhcy_jshen97_leochans_wangyp.crime',
              'henryhcy_jshen97_leochans_wangyp.light', 'henryhcy_jshen97_leochans_wangyp.eviction']

    @staticmethod
    def execute(trial=False):

        start_time = datetime.datetime.now()

        # set up database connection
        client = dml.pymongo.MongoClient()
        repo = client.repo
        repo.authenticate('henryhcy_jshen97_leochans_wangyp', 'henryhcy_jshen97_leochans_wangyp')

        # retrieve CVS, Walgreen, and 7-Eleven info through Google Places Search APIs
        # @see https://developers.google.com/places/web-service/search
        service = dml.auth['services']['googleprotocal']['service']

        # required parameters to specify for place searching @see Places API documentation
        key = "key="+dml.auth['services']['googleprotocal']['key']

        location = 'location=42.361145,-71.057083&'
        radius = 'radius=15000&'
        type = 'type=convenience_store&'

        keyword_cvs = "keyword=CVS&"
        keyword_walgreen = "input=Walgreen&"
        keyword_7eleven = "input=7-Eleven&"

        # retrieve cvs
        url_cvs = service+location+radius+type+keyword_cvs+key
        response_cvs = json.loads(urlopen(url_cvs).read().decode('utf-8'))
        res_dump_cvs = json.dumps(response_cvs, sort_keys=True, indent=2)

        data_cvs = response_cvs['results']
        for i in range(2):
            next_page_token = "&pagetoken="+response_cvs['next_page_token']
            url_next = service+location+radius+type+keyword_cvs+key+next_page_token
            response_cvs = json.loads(urlopen(url_next).read().decode('utf-8'))
            while (response_cvs['status'] == "INVALID_REQUEST"):
                time.sleep(.300)
                response_cvs = json.loads(urlopen(url_next).read().decode('utf-8'))
            data_cvs = data_cvs + response_cvs['results']

        repo.dropCollection('cvs')
        repo.createCollection('cvs')
        repo['henryhcy_jshen97_leochans_wangyp.cvs'].insert_many(data_cvs)
        repo['henryhcy_jshen97_leochans_wangyp.cvs'].metadata({'complete': True})
        repo['henryhcy_jshen97_leochans_wangyp.cvs'].delete_many({'status': 'INVALID_REQUEST'})

        #debug
        #count = 0;
        #for doc in repo['henryhcy_jshen97_leochans_wangyp.cvs'].find():
        #    pprint.pprint(doc)
        #    count+=1
        #print(count)
        print(repo['henryhcy_jshen97_leochans_wangyp.cvs'].metadata())

        # retrieve walgreen
        url_walgreen = service+location+radius+type+keyword_walgreen+key
        response_walgreen = json.loads(urlopen(url_walgreen).read().decode('utf-8'))
        res_dump_walgreen = json.dumps(response_walgreen, sort_keys=True, indent=2)

        data_walgreen = response_walgreen['results']
        for i in range(2):
            next_page_token = "&pagetoken="+response_walgreen['next_page_token']
            url_next = service+location+radius+type+keyword_walgreen+key+next_page_token
            response_walgreen = json.loads(urlopen(url_next).read().decode('utf-8'))
            while (response_walgreen['status'] == "INVALID_REQUEST"):
                time.sleep(.300)
                response_walgreen = json.loads(urlopen(url_next).read().decode('utf-8'))
            data_walgreen = data_walgreen + response_walgreen['results']

        repo.dropCollection('walgreen')
        repo.createCollection('walgreen')
        repo['henryhcy_jshen97_leochans_wangyp.walgreen'].insert_many(data_walgreen)
        repo['henryhcy_jshen97_leochans_wangyp.walgreen'].metadata({'complete': True})
        repo['henryhcy_jshen97_leochans_wangyp.walgreen'].delete_many({'status': 'INVALID_REQUEST'})

        #debug
        #count = 0;
        #for doc in repo['henryhcy_jshen97_leochans_wangyp.walgreen'].find():
        #   pprint.pprint(doc)
        #   count+=1
        #print(count)
        print(repo['henryhcy_jshen97_leochans_wangyp.walgreen'].metadata())


        # retrieve 7-Eleven
        url_7eleven = service+location+radius+type+keyword_7eleven+key
        response_7eleven = json.loads(urlopen(url_7eleven).read().decode('utf-8'))
        res_dump_7eleven = json.dumps(response_7eleven, sort_keys=True, indent=2)

        data_7eleven = response_7eleven['results']
        for i in range(2):
            next_page_token = "&pagetoken=" + response_7eleven['next_page_token']
            url_next = service + location + radius + type + keyword_7eleven + key + next_page_token
            response_7eleven = json.loads(urlopen(url_next).read().decode('utf-8'))
            while (response_7eleven['status'] == "INVALID_REQUEST"):
                time.sleep(.300)
                response_7eleven = json.loads(urlopen(url_next).read().decode('utf-8'))
            data_7eleven = data_7eleven + response_7eleven['results']

        repo.dropCollection('7eleven')
        repo.createCollection('7eleven')
        repo['henryhcy_jshen97_leochans_wangyp.7eleven'].insert_many(data_7eleven)
        repo['henryhcy_jshen97_leochans_wangyp.7eleven'].metadata({'complete': True})
        repo['henryhcy_jshen97_leochans_wangyp.7eleven'].delete_many({'status': 'INVALID_REQUEST'})

        #debug
        #count = 0;
        #for doc in repo['henryhcy_jshen97_leochans_wangyp.7eleven'].find():
        #  pprint.pprint(doc)
        #  count+=1
        #print(count)
        print(repo['henryhcy_jshen97_leochans_wangyp.7eleven'].metadata())

        # retrieve street light location
        url_light = "https://data.boston.gov/api/3/action/datastore_search?resource_id=c2fcc1e3-c38f-44ad-a0cf-e5ea2a6585b5"
        json_light = json.loads(urlopen(url_light).read().decode('utf-8'))
        json_dump_light = json.dumps(json_light, sort_keys=True, indent=2)
        repo.dropCollection('light')
        repo.createCollection('light')
        repo['henryhcy_jshen97_leochans_wangyp.light'].insert_one(json_light)
        repo['henryhcy_jshen97_leochans_wangyp.light'].metadata({'complete': True})
        #debug
        #pprint.pprint(repo['henryhcy_jshen97_leochans_wangyp.light'].find_one())
        print(repo['henryhcy_jshen97_leochans_wangyp.light'].metadata())

        # retrieve eviction boston
        url_eviction = "http://datamechanics.io/data/evictions_boston.csv"
        df_eviction = pd.read_csv(url_eviction, encoding='ISO-8859-1')
        json_eviction = json.loads(df_eviction.to_json(orient='records'))
        json_dump_eviction = json.dumps(json_eviction, sort_keys=True, indent=2)
        repo.dropCollection('eviction')
        repo.createCollection('eviction')
        repo['henryhcy_jshen97_leochans_wangyp.eviction'].insert_many(json_eviction)
        repo['henryhcy_jshen97_leochans_wangyp.eviction'].metadata({'complete': True})
        # debug
        #pprint.pprint(repo['henryhcy_jshen97_leochans_wangyp.eviction'].find_one())
        print(repo['henryhcy_jshen97_leochans_wangyp.eviction'].metadata())

        # retrieve crime.csv
        # @see: http://bpdnews.com/districts for district mapping
        url_crime = "http://datamechanics.io/data/crime.csv"
        df_crime = pd.read_csv(url_crime, encoding='ISO-8859-1')
        json_crime = json.loads(df_crime.to_json(orient='records'))
        json_dump_7eleven = json.dumps(json_crime, sort_keys=True, indent=2)
        repo.dropCollection('crime')
        repo.createCollection('crime')
        repo['henryhcy_jshen97_leochans_wangyp.crime'].insert_many(json_crime)
        repo['henryhcy_jshen97_leochans_wangyp.crime'].metadata({'complete': True})
        # debug
        #pprint.pprint(repo['henryhcy_jshen97_leochans_wangyp.cime'].find_one())
        print(repo['henryhcy_jshen97_leochans_wangyp.crime'].metadata())

        #print(repo.list_collection_names())
        repo.logout()

        end_time = datetime.datetime.now()

        return {"start": start_time, "end": end_time}

    @staticmethod
    def provenance(doc=prov.model.ProvDocument(), start_time=None, end_time=None):
        '''
            Create the provenance document describing everything happening
            in this script. Each run of the script will generate a new
            document describing that invocation event.
        '''

        client = dml.pymongo.MongoClient()
        repo = client.repo
        repo.authenticate('henryhcy_jshen97_leochans_wangyp', 'henryhcy_jshen97_leochans_wangyp')
        doc.add_namespace('alg', 'http://datamechanics.io/algorithm/')  # The scripts are in <folder>#<filename> format.
        doc.add_namespace('dat', 'http://datamechanics.io/data/')  # The data sets are in <user>#<collection> format.
        doc.add_namespace('ont', 'http://datamechanics.io/ontology#')  # 'Extension', 'DataResource', 'DataSet', 'Retrieval', 'Query', or 'Computation'.
        doc.add_namespace('log', 'http://datamechanics.io/log/')  # The event log.
        doc.add_namespace('ggl', 'https://maps.googleapis.com/maps/api/place/nearbysearch/json?')
        doc.add_namespace('dio', 'http://datamechanics.io/data/')
        doc.add_namespace('bdp', 'https://data.boston.gov/')

        this_script = doc.agent('alg:henryhcy_jshen97_leochans_wangyp#DataRetrieval',
                                {prov.model.PROV_TYPE: prov.model.PROV['SoftwareAgent'], 'ont:Extension': 'py'})
        resource_ggl = doc.entity('ggl:wc8w-nujj', {'prov:label': 'Places Search API', prov.model.PROV_TYPE: 'ont:DataResource', 'ont:Extension':'json'})
        resource_dio = doc.entity('dio:wc8w-nujk', {'prov:label': 'Data Mechanics IO', prov.model.PROV_TYPE: 'ont:DataResource', 'ont:Extension':'csv'})
        resource_bdp = doc.entity('bdp:c2fc-cle3', {'prov:label': 'Boston Data Portal', prov.model.PROV_TYPE: 'ont:DataResource', 'ont:Extension':'json'})

        get_cvs = doc.activity('log:uuid' + str(uuid.uuid4()), start_time, end_time)
        get_walgreen = doc.activity('log:uuid' + str(uuid.uuid4()), start_time, end_time)
        get_7eleven = doc.activity('log:uuid' + str(uuid.uuid4()), start_time, end_time)
        get_light = doc.activity('log:uuid' + str(uuid.uuid4()), start_time, end_time)
        get_eviction = doc.activity('log:uuid' + str(uuid.uuid4()), start_time, end_time)
        get_crime = doc.activity('log:uuid' + str(uuid.uuid4()), start_time, end_time)

        doc.wasAssociatedWith(get_cvs, this_script)
        doc.wasAssociatedWith(get_walgreen, this_script)
        doc.wasAssociatedWith(get_7eleven, this_script)
        doc.wasAssociatedWith(get_light, this_script)
        doc.wasAssociatedWith(get_eviction, this_script)
        doc.wasAssociatedWith(get_crime, this_script)

        doc.usage(get_cvs, resource_ggl, start_time, None,
                  {prov.model.PROV_TYPE: 'ont:Retrieval',
                   'ont:Query': 'location=42.361145,-71.057083&radius=8000& \
                                 type=convenience_store&keyword=CVS&key=API_KEY'
                   }
                  )
        doc.usage(get_walgreen, resource_ggl, start_time, None,
                  {prov.model.PROV_TYPE: 'ont:Retrieval',
                   'ont:Query': 'location=42.361145,-71.057083&radius=8000& \
                                 type=convenience_store&keyword=Walgreen&key=API_KEY'
                   }
                  )
        doc.usage(get_7eleven, resource_ggl, start_time, None,
                  {prov.model.PROV_TYPE: 'ont:Retrieval',
                   'ont:Query': 'location=42.361145,-71.057083&radius=8000& \
                                 type=convenience_store&keyword=7-Eleven&key=API_KEY'
                   }
                  )
        doc.usage(get_light, resource_bdp, start_time, None,
                  {prov.model.PROV_TYPE: 'ont:Retrieval',
                   'ont:Query': 'api/3/action/datastore_search?resource_id=c2fcc1e3-c38f-44ad-a0cf-e5ea2a6585b5 \
                                &$format=json'
                   }
                  )
        doc.usage(get_eviction, resource_dio, start_time, None,
                  {prov.model.PROV_TYPE: 'ont:Retrieval',
                   'ont:Query': 'evictions_boston.csv'
                   }
                  )
        doc.usage(get_crime, resource_dio, start_time, None,
                  {prov.model.PROV_TYPE: 'ont:Retrieval',
                   'ont:Query': 'crime.csv'
                   }
                  )

        cvs = doc.entity('dat:henryhcy_jshen97_leochans_wangyp#cvs',
                          {prov.model.PROV_LABEL: 'CVS', prov.model.PROV_TYPE: 'ont:DataSet'})
        doc.wasAttributedTo(cvs, this_script)
        doc.wasGeneratedBy(cvs, get_cvs, end_time)
        doc.wasDerivedFrom(cvs, resource_ggl, get_cvs, get_cvs, get_cvs)

        walgreen = doc.entity('dat:henryhcy_jshen97_leochans_wangyp#walgreen',
                         {prov.model.PROV_LABEL: 'Walgreen', prov.model.PROV_TYPE: 'ont:DataSet'})
        doc.wasAttributedTo(walgreen, this_script)
        doc.wasGeneratedBy(walgreen, get_walgreen, end_time)
        doc.wasDerivedFrom(walgreen, resource_ggl, get_walgreen, get_walgreen, get_walgreen)

        seven_eleven = doc.entity('dat:henryhcy_jshen97_leochans_wangyp#seven_eleven',
                         {prov.model.PROV_LABEL: '7Eleven', prov.model.PROV_TYPE: 'ont:DataSet'})
        doc.wasAttributedTo(seven_eleven, this_script)
        doc.wasGeneratedBy(seven_eleven, get_7eleven, end_time)
        doc.wasDerivedFrom(seven_eleven, resource_ggl, get_7eleven, get_7eleven, get_7eleven)

        street_light = doc.entity('dat:henryhcy_jshen97_leochans_wangyp#street_light',
                                  {prov.model.PROV_LABEL: 'Street Light', prov.model.PROV_TYPE: 'ont:DataSet'})
        doc.wasAttributedTo(street_light, this_script)
        doc.wasGeneratedBy(street_light, get_light, end_time)
        doc.wasDerivedFrom(street_light, resource_bdp, get_light, get_light, get_light)

        eviction = doc.entity('dat:henryhcy_jshen97_leochans_wangyp#eviction',
                              {prov.model.PROV_LABEL: 'Evictions Boston', prov.model.PROV_TYPE: 'ont:DataSet'})
        doc.wasAttributedTo(eviction, this_script)
        doc.wasGeneratedBy(eviction, get_eviction, end_time)
        doc.wasDerivedFrom(eviction, resource_dio, get_eviction, get_eviction, get_eviction)

        crime_log = doc.entity('dat:henryhcy_jshen97_leochans_wangyp#crime_log',
                         {prov.model.PROV_LABEL: 'Crime Log', prov.model.PROV_TYPE: 'ont:DataSet'})
        doc.wasAttributedTo(crime_log, this_script)
        doc.wasGeneratedBy(crime_log, get_crime, end_time)
        doc.wasDerivedFrom(crime_log, resource_dio, get_crime, get_crime, get_crime)

        repo.logout()

        return doc

# debug

'''
DataRetrieval.execute()
doc = DataRetrieval.provenance()
print(doc.get_provn())
print(json.dumps(json.loads(doc.serialize()), indent=4))
'''
