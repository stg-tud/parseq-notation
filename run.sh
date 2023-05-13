sh run-coq.sh
sh run-scala.sh

if [ -z "$HOST_UID" ]; then
  echo no host uid found...
else
  echo change ownership to $HOST_UID
  chown -R $HOST_UID:$HOST_UID .
fi
