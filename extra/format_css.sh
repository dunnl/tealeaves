find html-examples -iname "*.html"  -exec sed -i \
     -e 's#alectryon\.css#../alectryon.css#g' \
     -e 's#alectryon\.js#../alectryon.js#g' \
     -e 's#docutils_basic\.css#../docutils_basic.css#g' \
     -e 's#pygments\.css#../pygments.css#g' \
     {} \;
