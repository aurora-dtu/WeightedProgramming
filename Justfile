manual:
    cd manual; lake exe docs

serve-manual:
    miniserve --port 8081 --index index.html manual/_out/html-multi/
