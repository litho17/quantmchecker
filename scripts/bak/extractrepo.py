import json
import requests
import ssl

# python3 extractrepo.py

# keyword = 'import org.springframework.boot'
# keyword = 'import org.springframework.web'
# keyword = 'import play.'
# keyword = 'import play.mvc'
# keyword = 'import org.eclipse.jetty'
# keyword = 'import org.eclipse.jetty.server'
# keyword = 'import io.dropwizard'
# keyword = 'import static spark.Spark'

keyword = 'import org.springframework.stereotype.Controller'
# https://www.journaldev.com/2888/spring-tutorial-spring-core-tutorial#spring-mvc-tutorial

# keyword = 'import org.apache.struts2.convention.annotation.Action'
# https://www.journaldev.com/2310/struts-2-tutorial

# keyword = 'import org.eclipse.jetty.server.handler.AbstractHandler'

# keyword = 'import play.mvc.Controller'
# https://www.playframework.com/documentation/1.3.0-RC1/firstapp

# keyword = 'import io.dropwizard.Application'
# http://www.dropwizard.io/0.9.2/docs/getting-started.html

# Simple JSON: yylex()
# https://github.com/fangyidong/json-simple/blob/master/src/main/java/org/json/simple/parser/Yylex.java

keyword = 'import okhttp3'

username = 'litho17'
password = 'orc19940119'
auth = (username, password)

for pageNum in range(1, 11):
	params = (
	    ('q', keyword),
	    ('type', 'Code'),
	    ('language', 'java'),
	    ('per_page', '100'),
	    ('page', pageNum)
	)
	search_url = "https://api.github.com/search/code"
	data = requests.get(search_url, auth=auth, params=params).json()
	print("Page: " + str(pageNum))
	print("Total count: " + str(data["total_count"]))

	try:
		for item in data["items"]:
			# for i in item["repository"]:
			#	print i
			repo_url = item["repository"]["url"]
			response = requests.get(repo_url, auth=auth)
			json = response.json()
			# print(json["stargazers_count"])
			if json["stargazers_count"] >= 10:
				print("["+ str(json["stargazers_count"]) + " stars] "+ json["html_url"])
	except Exception as inst:
		# print(data)
		print(type(inst))
		print(inst.args)
		print(inst)

# Setup for Mac (When you cannot do `brew link --force openssl`)
# `brew install openssl`
# `brew install python --with-brewed-openssl`
# Rename /usr/bin/openssl to /usr/local/openssl.bak
# Link /usr/bin/openssl to /usr/local/Cellar/openssl/1.0.2o_1/bin/openssl


# References: 
# https://curl.trillworks.com/
# https://www.twilio.com/blog/2016/12/http-requests-in-python-3.html