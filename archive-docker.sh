set -e
cd ..

PROJ=par-seq-notation
TMP=tmp-docker

echo ============================================================================================
echo now building the docker image
echo ============================================================================================
[ -e "$TMP" ] && rm -r "$TMP"
cp -R src "$TMP"
cd "$TMP"
docker build -t "$PROJ" .
cd ..
docker save "$PROJ" -o docker-image.tar
#docker-squash "$PROJ" -f a3cc2d767bf1 -t "$PROJ"-squashed --output-path docker-image.tar # squash from layer TODO
echo ============================================================================================
echo now testing whether the docker image works
echo ============================================================================================
[ -e "$TMP" ] && rm -r "$TMP"
cp -R src "$TMP"
#docker container rm -f $(docker ps -a -q --filter="ancestor=$PROJ")
docker image rm "$PROJ"
docker load -i docker-image.tar
docker run -it -e HOST_UID=$(id -u) -v "$PWD"/"$TMP":/app "$PROJ"

echo ============================================================================================
echo compressing
echo ============================================================================================
rm -f "$PROJ".tar.gz
tar -czvf "$PROJ".tar.gz src docker-image.tar

#tar --exclude='./PrismaFiles/DockerEvaluations/*' ... # exlude TODO stuff

