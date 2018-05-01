import json
import requests
import ssl

# python3 extractrepo.py


# data = json.load(open('a.json'))
# print(ssl.OPENSSL_VERSION)

for pageNum in range(1, 1000000):
	auth = ('litho17', 'orc19940119')
	params = (
	    ('q', 'import org.springframework.boot'),
	    ('type', 'Code'),
	    ('language', 'java'),
	    ('per_page', '100'),
	    ('page', pageNum)
	)
	url = "https://api.github.com/search/code"
	print(pageNum)
	data = requests.get(url, auth=auth, params=params).json()

	try:
		# print(len(data["items"]))
		for item in data["items"]:
			# for i in item["repository"]:
			#	print i
			url = item["repository"]["url"]
			response = requests.get(url, auth=auth)
			json = response.json()
			# print(json["stargazers_count"])
			if json["stargazers_count"] > 10:
				print(json["html_url"])
	except Exception as inst:
		print(data)
		print(type(inst))
		print(inst.args)
		print(inst)

# References: 
# https://curl.trillworks.com/
# https://www.twilio.com/blog/2016/12/http-requests-in-python-3.html