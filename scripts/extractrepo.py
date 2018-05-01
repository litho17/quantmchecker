import json
import requests
import ssl

# python3 extractrepo.py


# data = json.load(open('a.json'))
# print(ssl.OPENSSL_VERSION)

auth = ('litho17', 'orc19940119')
params = (
    ('q', 'import org.springframework.boot'),
    ('type', 'Code'),
)
url = "https://api.github.com/search/code"
data = requests.get(url, auth=auth, params=params).json()

print((data["items"]))
for item in data["items"]:
	# for i in item["repository"]:
	#	print i
	url = item["repository"]["url"]
	response = requests.get(url, auth=auth)
	json = response.json()
	# print(json["stargazers_count"])
	if json["stargazers_count"] > 10:
		print(json["html_url"])

# References: 
# https://curl.trillworks.com/
# https://www.twilio.com/blog/2016/12/http-requests-in-python-3.html