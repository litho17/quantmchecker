#!/bin/sh

credential="litho17:orc19940119"

curl -u $credential "https://api.github.com/search/code?q=import+org.springframework.boot&type=Code"
#curl -u $credential "https://api.github.com/repos/feynmanliang/bachbot/stargazers"

# https://github.com/EdmundLeex/learning-java/stargazers
# https://stackoverflow.com/questions/24132790/how-to-search-for-code-in-github-with-github-api
# https://gist.github.com/jasonrudolph/6065289
# https://developer.github.com/v3/search/#search-code
# https://api.github.com/users/EdmundLeex/starred
# https://github.com/search?utf8=%E2%9C%93&q=%22import+org.springframework.boot%22+stars%3A%3E1&type=Code
# https://github.com/search?l=&q=%22import+org.springframework.boot%22+language%3AJava&type=Code
# https://help.github.com/articles/searching-code/
# https://developer.github.com/v3/guides/getting-started/
# https://developer.github.com/v3/#authentication
