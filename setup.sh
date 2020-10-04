cd obj
sed -i -e "s/LIBS=/LIBS=-lcrypto -lcrypto -ldl -ltepla -lcrypto -lgmp /g" Rules
c
make
make install
cd ..
